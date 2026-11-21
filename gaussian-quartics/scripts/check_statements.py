"""Check that the compared statements, and the definitions they use, are those of the library as Codex produced it.

The reference is the first commit of this repository (REFERENCE below), which holds the Lean project exactly as
Codex produced it. Since then the three anonymous instances used by the Challenge were given names (`instance : T`
became `instance name : T`), so that the Challenge and the library give them the same constant names. For every
declaration that `make_challenge.py` copies or states, this script compares its text, as the Challenge uses it, at
REFERENCE and in the working tree; instance names are ignored.
Run from the project directory: python3 scripts/check_statements.py
"""
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from make_challenge import BLOCKS, blocks_of, find, sorried  # noqa: E402

REFERENCE = '3c51761913392787e6a01e66ac65e3f961db7d68'
PROJECT = 'gaussian-quartics'


def unnamed(text):
    return re.sub(r'^instance \w+ :', 'instance :', text, flags=re.M)


def at_reference(name, current, text):
    """The declaration at REFERENCE; an instance, unnamed there, is found by its header."""
    if not current.lstrip().startswith('instance'):
        return find(text, name, f'{REFERENCE[:7]}')
    header = unnamed(current).split(':=')[0]
    hits = [b for b in blocks_of(text) if b.split(':=')[0] == header]
    if len(hits) != 1:
        raise SystemExit(f'{name}: {len(hits)} matching instances at {REFERENCE[:7]}')
    return hits[0]


if __name__ == '__main__':
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
    bad = n = 0
    for path, _section, _opens, decls in BLOCKS:
        old = subprocess.run(['git', 'show', f'{REFERENCE}:{PROJECT}/{path}'], capture_output=True, text=True,
                             check=True).stdout
        for name, mode in decls:
            now = find(open(path).read(), name, path)
            then = at_reference(name, now, old)
            if mode != 'copy':
                now, then = sorried(now, name), sorried(then, name)
            n += 1
            if unnamed(now) != unnamed(then):
                bad += 1
                print(f'CHANGED: {name} ({path})')
    print(f'{n} declarations compared with {REFERENCE[:7]}: ' + ('OK' if not bad else f'{bad} changed'))
    sys.exit(1 if bad else 0)
