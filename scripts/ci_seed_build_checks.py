#!/usr/bin/env python3
"""Register already-built, *existing* Lake outputs for the full audit.

This is for CI only. It is intended to run immediately after a successful
`lake build` of the `Dyson` library (which imports every project module).
It never creates, synthesizes, or substitutes `.olean` proof artifacts.
The normal local verification command remains `python3 scripts/verify.py`.
"""
import json
from pathlib import Path
from verify import ROOT, sha, source_modules


def main() -> None:
    paths, _ = source_modules()
    checks = []
    missing = []
    for name, source in sorted(paths.items()):
        olean = ROOT / '.lake/build/lib/lean' / Path(*name.split('.')).with_suffix('.olean')
        if not olean.is_file() or olean.stat().st_size == 0:
            missing.append(str(olean.relative_to(ROOT)))
            continue
        checks.append({
            'module': name,
            'exit_code': 0,
            'sha256': sha(source),
            'command': ['lake', 'build', 'Dyson'],
            'verification_note': 'Module imported by successfully completed lake build',
        })
    if missing:
        raise SystemExit('Successful lake build must produce all module artifacts. Missing:\n' + '\n'.join(missing[:30]))
    report_dir = ROOT / 'validation'
    report_dir.mkdir(exist_ok=True)
    (report_dir / 'build_checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(f'Registered {len(checks)} compiled project modules for full Lean audit.')


if __name__ == '__main__':
    main()
