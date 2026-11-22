"""Check that the compared statements, and the definitions they use, are those of the library as Codex produced it.

The reference is the commit of this repository that added the Lean project exactly as Codex produced it
(REFERENCE below). For every declaration that `make_challenge.py` copies or states, this script compares its text,
as the Challenge uses it (for a theorem: the statement, without the proof), at REFERENCE and in the working tree.
Run from the project directory: python3 scripts/check_statements.py
"""
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from make_challenge import BLOCKS, find, sorried  # noqa: E402

REFERENCE = '8fe5b9a0dc2172ef13b40fcbcc35ddbeddf851d1'
PROJECT = 'three-factorials'


if __name__ == '__main__':
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
    bad = n = 0
    for path, _section, _opens, decls in BLOCKS:
        old = subprocess.run(['git', 'show', f'{REFERENCE}:{PROJECT}/{path}'], capture_output=True, text=True,
                             check=True).stdout
        for name, mode in decls:
            now = find(open(path).read(), name, path)
            then = find(old, name, f'{REFERENCE[:7]}:{path}')
            if mode != 'copy':
                now, then = sorried(now, name), sorried(then, name)
            n += 1
            if now != then:
                bad += 1
                print(f'CHANGED: {name} ({path})')
    print(f'{n} declarations compared with {REFERENCE[:7]}: ' + ('OK' if not bad else f'{bad} changed'))
    sys.exit(1 if bad else 0)
