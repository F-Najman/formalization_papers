"""Check that the compared statements, and the declarations they use, are those of the library as Codex produced it.

The reference is the commit of this repository that holds the Lean project exactly as Codex produced it (REFERENCE
below). For every declaration that `make_challenge.py` copies into Challenge.lean, this script checks that its text
(docstring and attributes included) occurs verbatim in the same source file at REFERENCE; for every declaration that
the Challenge states with `sorry`, it checks the same for its statement, up to the `:=` that starts the proof. Since
REFERENCE, the library changed only in one import (TorsionToMarked.lean: `public import Mathlib.Algebra.Field.ZMod`,
so that the statements there and in the Challenge elaborate with the same instances); no declaration changed.
Run from the project directory, after `lake build`: python3 scripts/check_statements.py
"""
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from make_challenge import NS, TARGETS, decl_text, lean_deps, path_of, sorried  # noqa: E402

REFERENCE = 'c95be2528c117c9f7a99613e763876843d2b4ffc'
PROJECT = 'najman-trbovic'


def at_reference(path):
    return subprocess.run(['git', 'show', f'{REFERENCE}:{PROJECT}/{path}'], capture_output=True, text=True,
                          check=True).stdout


if __name__ == '__main__':
    os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
    names = [n for _, decls in TARGETS for n, _ in decls]
    rows = lean_deps(names)
    old, now = {}, {}
    bad = n = 0
    for r in rows:
        path = path_of(r['module'])
        if path not in old:
            old[path] = at_reference(path)
            now[path] = open(path).read().split('\n')
        copy = r['role'] == 'dep' and not (r['kind'] == 'theorem' and re.search(
            r'^(theorem|lemma) ', decl_text(now[path], r, False), re.M))
        text = decl_text(now[path], r, copy)
        if not copy:
            text = sorried(text, r['name'])[:-len(':= sorry\n')]
        n += 1
        if text not in old[path] or (not copy and text + ':=' not in old[path]):
            bad += 1
            print(f'CHANGED: {r["name"]} ({path})')
    print(f'{n} declarations ({sum(r["role"] == "target" for r in rows)} compared results) checked against '
          f'{REFERENCE[:7]}: ' + ('OK' if not bad else f'{bad} changed'))
    sys.exit(1 if bad else 0)
