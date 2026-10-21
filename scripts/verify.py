#!/usr/bin/env python3
"""Compile every delivered module, then audit every named theorem.

python3 scripts/verify.py --prepare     # refresh aggregators and audit sources
python3 scripts/verify.py               # complete fresh build and audit
python3 scripts/verify.py --audit-only  # only if all source hashes match build_checks.json
python3 scripts/verify.py --incremental # rebuild source changes and all dependent modules

No proof placeholder, project axiom, native_decide, or unsafe code is accepted.
The axiom check does NOT discharge theorem hypotheses: see EXTERNAL_ARGUMENTS.md.
"""
from __future__ import annotations
import argparse, concurrent.futures, hashlib, json, re, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
ROOT = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def code_only(text: str) -> str:
    """Remove nested Lean block comments, line comments, and string literals."""
    result = []
    i, depth = 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            result.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            result.extend("  ")
            i += 2
        elif depth:
            result.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            result.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            result.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    result.extend("  ")
                    i += 2
                elif text[i] == '"':
                    result.append(" ")
                    i += 1
                    break
                else:
                    result.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def source_modules():
    paths = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
             for p in (ROOT/'Dyson').rglob('*.lean')}
    paths['Dyson'] = ROOT/'Dyson.lean'
    deps = {m: [d for d in re.findall(r'^import\s+(\S+)', code_only(p.read_text()), re.M)
                if d == 'Dyson' or d.startswith('Dyson.')] for m,p in paths.items()}
    for m, ds in deps.items():
        for d in ds:
            if d not in paths: raise RuntimeError(f'Missing dependency {d} of {m}')
    return paths,deps

def write_audit_sources(declarations):
    """Use actual environment Names for private declarations with numeric components."""
    public=[d['name'] for d in declarations if d['visibility']=='public']
    private=[d for d in declarations if d['visibility']=='private']
    header='import Dyson\nset_option pp.privateNames true\n'
    axiom_source=header+'\n'+''.join('#print axioms '+n+'\n' for n in public)
    signature_source=header+'set_option pp.universes true\nset_option format.width 120\n\n'+''.join('#check '+n+'\n' for n in public)
    if private:
        queries=', '.join('('+json.dumps('_private.'+d['module']+'.')+', '+json.dumps('.'+d['source_name'])+')' for d in private)
        traversal=('\nopen Lean Elab Command\nrun_cmd do\n'+
            '  let env ← getEnv\n  let queries : List (String × String) := ['+queries+']\n'+
            '  let mut count := 0\n'+
            '  for (n, _) in env.constants.toList do\n'+
            '    for (pre, suf) in queries do\n'+
            '      if n.toString.startsWith pre && n.toString.endsWith suf then\n'+
            '        let some (.thmInfo ci) := env.checked.get.find? n\n'+
            '          | throwError "Expected a kernel-checked private theorem: {n}"\n'+
            '        count := count + 1\n')
        end=('  unless count == queries.length do\n'+
             '    throwError "Private theorem count mismatch: {count} != {queries.length}"\n')
        signature_source+=traversal+'        logInfo m!"{n} : {ci.type}"\n'+end
        axiom_source+=traversal+('        let axioms ← collectAxioms n\n'+
            '        if axioms.isEmpty then\n'+
            '          logInfo m!"\'{n}\' does not depend on any axioms"\n'+
            '        else\n'+
            '          logInfo m!"\'{n}\' depends on axioms: {axioms.qsort Name.lt |>.toList}"\n')+end
    (ROOT/'AxiomAudit.lean').write_text(axiom_source)
    (ROOT/'SignatureAudit.lean').write_text(signature_source)

def prepare():
    for subtree in ['Full','Paper']:
        directory=ROOT/'Dyson'/subtree
        if directory.is_dir():
            modules=sorted('.'.join(p.relative_to(ROOT).with_suffix('').parts)
                           for p in directory.rglob('*.lean'))
            (ROOT/'Dyson'/f'{subtree}.lean').write_text('\n'.join('import '+m for m in modules)+'\n')
    top=sorted('Dyson.'+p.stem for p in (ROOT/'Dyson').glob('*.lean'))
    (ROOT/'Dyson.lean').write_text('\n'.join('import '+m for m in top)+'\n')
    paths,deps=source_modules()
    declarations=[]
    for module,p in sorted(paths.items()):
        code=code_only(p.read_text())
        bad=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',code)
        if bad: raise RuntimeError(f'Forbidden proof escape in {p}: {bad}')
        namespaces=[]
        for line_number,line in enumerate(code.splitlines(),1):
            m=re.match(r'\s*namespace\s+([^\s]+)',line)
            if m: namespaces.append(m.group(1)); continue
            m=re.match(r'\s*end\s+([^\s]+)',line)
            if m and namespaces and namespaces[-1]==m.group(1):
                namespaces.pop(); continue
            m=re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:(?:protected|private)\s+)?(theorem|lemma)\s+([^\s(:{\[]+)",line)
            if m:
                declarations.append({'name':'.'.join(namespaces+[m.group(2)]),
                                     'source_name':'.'.join(namespaces+[m.group(2)]),
                                     'visibility':'private' if re.search(r'\bprivate\s+(?:theorem|lemma)',line) else 'public',
                                     'module':module,'file':str(p.relative_to(ROOT)),
                                     'line':line_number,'kind':m.group(1)})
            elif re.search(r'\b(?:theorem|lemma)\s+[^\s(:{\[]+',line):
                raise RuntimeError(f'Unparsed theorem declaration: {p}:{line_number}')
            else:
                # Lean's one-name alias command also introduces a checked
                # theorem, so include it in both type and dependency audits.
                alias=re.match(r'\s*alias\s+([^\s]+)\s*:=\s*(\S+)',line)
                if alias:
                    name='.'.join(namespaces+[alias.group(1)])
                    declarations.append({'name':name, 'source_name':name,
                                         'visibility':'public','module':module,
                                         'file':str(p.relative_to(ROOT)),
                                         'line':line_number,'kind':'alias',
                                         'alias_target':alias.group(2)})
                elif re.match(r'\s*alias\b',line):
                    raise RuntimeError(f'Unparsed theorem alias: {p}:{line_number}')
    names=[d['name'] for d in declarations]
    if len(names)!=len(set(names)): raise RuntimeError('Duplicate parsed theorem names')
    write_audit_sources(declarations)
    inventory={'note':'Named theorem inventory, not a claim that every paper result is complete.',
               'module_count':len(paths),'theorem_count':len(names),'declarations':declarations}
    (ROOT/'theorem_inventory.json').write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n')
    return paths,deps,declarations

def command(*args):
    return ['bash',str(ROOT/'scripts/lean-env.sh'),'lake','env','lean',*map(str,args)]

def resolve_private_declarations(paths,declarations,logdir):
    """Read actual private kernel names from the compiled Lean environment."""
    private=[d for d in declarations if d['visibility']=='private']
    if private:
        queries=', '.join('('+json.dumps('_private.'+d['module']+'.')+', '+json.dumps('.'+d['source_name'])+')' for d in private)
        discovery=ROOT/'PrivateAuditDiscovery.lean'
        discovery.write_text('import Dyson\nopen Lean Elab Command\nrun_cmd do\n'+
            '  let env ← getEnv\n  let queries : List (String × String) := ['+queries+']\n'+
            '  for (n, _) in env.constants.toList do\n    let s := n.toString\n'+
            '    for (pre, suf) in queries do\n'+
            '      if s.startsWith pre && s.endsWith suf then\n'+
            '        logInfo m!"PRIVATE_DECL {s}"\n')
        result=subprocess.run(command(discovery),cwd=ROOT,text=True,
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (logdir/'private_name_discovery.log').write_text(result.stdout)
        if result.returncode: raise RuntimeError(result.stdout)
        found=re.findall(r'PRIVATE_DECL (\S+)',result.stdout)
        for d in private:
            matches=[n for n in found if n.startswith('_private.'+d['module']+'.') and n.endswith('.'+d['source_name'])]
            if len(matches)!=1: raise RuntimeError(f'Private kernel name ambiguous or missing: {d}')
            d['name']=matches[0]
    names=[d['name'] for d in declarations]
    write_audit_sources(declarations)
    inventory={'note':'Includes public and private named theorems; see CORRESPONDENCE.md for paper entry points.',
               'module_count':len(paths),'theorem_count':len(names),
               'private_theorem_count':len(private),'declarations':declarations}
    (ROOT/'theorem_inventory.json').write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n')

def compile_one(module,p,logdir):
    before=sha(p)
    out=ROOT/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
    out.parent.mkdir(parents=True,exist_ok=True)
    cmd=command('-o',out,p)
    result=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (logdir/(module+'.log')).write_text(result.stdout)
    after=sha(p)
    if before!=after: raise RuntimeError(f'Source changed during compilation: {module}')
    return {'module':module,'exit_code':result.returncode,'sha256':after,'command':cmd}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare',action='store_true')
    parser.add_argument('--audit-only',action='store_true')
    parser.add_argument('--incremental',action='store_true',help='reuse matching hashes and rebuild every transitive dependent of a changed module')
    parser.add_argument('--keep-going',action='store_true',help='record failures and continue independent modules; a failed build never passes the audit')
    parser.add_argument('--individual-axioms',action='store_true',help='use separate #print axioms commands; the default traverses their exact joint dependency closure with a shared visited set')
    args=parser.parse_args()
    paths,deps,declarations=prepare()
    if args.prepare:
        print(f'Prepared {len(paths)} modules and {len(declarations)} named theorem audits.'); return 0
    logdir=ROOT/'validation'; logdir.mkdir(exist_ok=True)
    checksfile=logdir/'build_checks.json'
    if not args.audit_only:
        pending=set(paths); completed=set(); running={}; checks=[]
        if args.incremental and checksfile.exists():
            prior={x['module']:x for x in json.loads(checksfile.read_text())}
            dirty={m for m,p in paths.items() if m not in prior or prior[m]['exit_code'] or prior[m]['sha256']!=sha(p)
                   or not (ROOT/'.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.olean')).exists()}
            changed=True
            while changed:
                more={m for m,ds in deps.items() if any(d in dirty for d in ds)}-dirty
                changed=bool(more); dirty.update(more)
            completed=set(paths)-dirty; pending=dirty
            checks=[prior[m] for m in sorted(completed)]
            print(f'Reusing {len(completed)} unchanged verified modules; rebuilding {len(dirty)} modules/dependents.',flush=True)
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            while pending or running:
                for m in sorted(pending):
                    if len(running)>=2: break
                    if all(d in completed for d in deps[m]):
                        running[pool.submit(compile_one,m,paths[m],logdir)]=m
                        pending.remove(m)
                        print('START '+m,flush=True)
                if not running:
                    if any(x['exit_code'] for x in checks):
                        print(f'{len(pending)} modules blocked by failed dependencies.',flush=True)
                        break
                    raise RuntimeError('Dependency cycle: '+str(pending))
                done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
                for future in done:
                    m=running.pop(future); check=future.result(); checks.append(check)
                    checksfile.write_text(json.dumps(checks,indent=2)+'\n')
                    print(('CHECKED ' if check['exit_code']==0 else 'FAILED ')+m,flush=True)
                    if check['exit_code']:
                        print((logdir/(m+'.log')).read_text())
                        if not args.keep_going: return 1
                        continue
                    completed.add(m)
        checksfile.write_text(json.dumps(checks,indent=2)+'\n')
        if any(x['exit_code'] for x in checks): return 1
    else:
        checks=json.loads(checksfile.read_text())
    checkmap={x['module']:x for x in checks}
    if set(checkmap)!=set(paths): raise RuntimeError('Module inventory changed; fresh build required')
    for m,p in paths.items():
        if checkmap[m]['exit_code'] or checkmap[m]['sha256']!=sha(p):
            raise RuntimeError(f'Stale build for {m}; fresh build required')
    resolve_private_declarations(paths,declarations,logdir)
    names=[d['name'] for d in declarations]
    if args.individual_axioms:
        audit_path=ROOT/'AxiomAudit.lean'
    else:
        audit_path=ROOT/'JointAxiomAudit.lean'
        audit_path.write_text('import Dyson\nopen Lean Elab Command\nrun_cmd do\n'+
            '  let env ← getEnv\n  let names : List String := ['+', '.join(json.dumps(n,ensure_ascii=False) for n in names)+']\n'+
            '  let expected := names.foldl (fun s n => s.insert n) ({} : Std.HashSet String)\n'+
            '  let mut roots : Array Name := #[]\n'+
            '  for (n, _) in env.constants.toList do\n'+
            '    if expected.contains n.toString then\n'+
            '      match env.checked.get.find? n with\n'+
            '      | some (.thmInfo _) => roots := roots.push n\n'+
            '      | _ => throwError "Expected a kernel-checked theorem: {n}"\n'+
            '  unless roots.size == names.length do\n'+
            '    throwError "Theorem root count mismatch: {roots.size} != {names.length}"\n'+
            '  let action : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect\n'+
            '  let (_, state) := (action.run env).run {}\n'+
            '  for a in state.axioms do\n    logInfo m!"JOINT_AXIOM {a}"\n'+
            '  for n in roots do\n    logInfo m!"AUDITED_THEOREM {n}"\n')
    audit=subprocess.run(command(audit_path),cwd=ROOT,text=True,
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (logdir/'axiom_audit.log').write_text(audit.stdout)
    used=set()
    if args.individual_axioms:
        for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',audit.stdout,re.S):
            used.update(x.strip() for x in group.split(',') if x.strip())
        audited=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",audit.stdout)
    else:
        used=set(re.findall(r'JOINT_AXIOM (\S+)',audit.stdout))
        audited=re.findall(r'AUDITED_THEOREM (\S+)',audit.stdout)
    extra=sorted(used-STANDARD_AXIOMS)
    signatures=subprocess.run(command(ROOT/'SignatureAudit.lean'),cwd=ROOT,text=True,
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (logdir/'theorem_signatures.log').write_text(signatures.stdout)
    routes=subprocess.run(command(ROOT/'ProofRouteAudit.lean'),cwd=ROOT,text=True,
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (logdir/'proof_routes.log').write_text(routes.stdout)
    route_count=len(re.findall(r'^ROUTE_PASS ',routes.stdout,re.M))
    passed=audit.returncode==0 and signatures.returncode==0 and routes.returncode==0 and route_count>0 and len(audited)==len(declarations) and set(audited)==set(names) and not extra
    report={'verified_at_utc':datetime.now(timezone.utc).isoformat(),
            'scope':'Whole-article formalization project relative to explicitly listed external arguments; consult CORRESPONDENCE.md and FORMALIZATION_STATUS.md for scope.',
            'lean_version':'4.24.0','mathlib_revision':'f897ebcf72cd16f89ab4577d0c826cd14afaafc7',
            'original_tex_sha256':sha(ROOT/'source/main-article-1014.tex'),
            'formalized_tex_sha256':sha(ROOT/'source/main-article-1014.formalized.tex'),
            'module_count':len(paths),'theorem_count':len(declarations),
            'module_checks':checks,'axiom_audit_exit_code':audit.returncode,
            'signature_audit_exit_code':signatures.returncode,'audited_declaration_count':len(audited),
            'proof_route_audit_exit_code':routes.returncode,'checked_proof_routes':route_count,
            'proof_route_audit_sha256':sha(ROOT/'ProofRouteAudit.lean'),
            'axiom_audit_method':'individual #print axioms' if args.individual_axioms else 'Lean.CollectAxioms.collect over every named theorem with one shared visited set',
            'private_theorem_count':sum(d['visibility']=='private' for d in declarations),
            'axioms_used':sorted(used),'unexpected_axioms':extra,
            'no_forbidden_proof_escapes':True,'passed':passed,
            'assumption_warning':'Explicit theorem hypotheses are not included in #print axioms. Review SignatureAudit.lean and EXTERNAL_ARGUMENTS.md.'}
    (logdir/'verification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(f'Audit {"PASS" if passed else "FAIL"}: {len(paths)} modules, {len(declarations)} named theorems; axioms {sorted(used)}')
    if not passed:
        for label, result in [('axiom_audit',audit),('theorem_signatures',signatures),('proof_routes',routes)]:
            errors=[line for line in result.stdout.splitlines() if re.search(r'\berror:',line)]
            print(f'{label}: exit {result.returncode}; full log: {logdir/(label+".log")}')
            print('\n'.join(errors[:20]))
    return 0 if passed else 1

if __name__=='__main__':
    raise SystemExit(main())
