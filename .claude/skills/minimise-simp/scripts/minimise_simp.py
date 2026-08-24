#!/usr/bin/env python3
"""Find which arguments of a `simp only [...]` call are load-bearing.

Builds one scratch file containing N copies of the enclosing declaration, copy
`i` having lemma `i` dropped, and compiles it in a single `lake env lean` run.
A copy that compiles clean means that lemma is individually removable.

    python3 minimise_simp.py <file.lean> <line-of-simp-only>          # batch pass
    python3 minimise_simp.py <file.lean> <line> --keep A,B,C          # verify a set

Run from the repo root. Removals are not always independent, so after dropping
everything the batch pass cleared, re-run with --keep to confirm the survivors.
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

DECL_START = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                        r"(theorem|lemma|example)\b")
# A new top-level item ends the declaration we are working on.
DECL_END = re.compile(r"^(theorem|lemma|example|abbrev|def|instance|structure|inductive|"
                      r"end\b|namespace\b|section\b|open\b|#|/--|/-!|@\[)")


def find_decl(lines, idx):
    """Return (start, end) line indices of the declaration containing `idx`."""
    start = None
    for i in range(idx, -1, -1):
        if DECL_START.match(lines[i]):
            start = i
            break
    if start is None:
        sys.exit(f"error: no theorem/lemma/example found at or above line {idx + 1}")
    end = len(lines)
    for i in range(idx + 1, len(lines)):
        if DECL_END.match(lines[i]):
            end = i
            break
    # Trim trailing blank lines so variants stay tightly packed.
    while end > idx + 1 and not lines[end - 1].strip():
        end -= 1
    return start, end


def parse_simp(lines, idx):
    """Return (span_end, args) for the `simp only [...]` starting at line `idx`.

    `span_end` is exclusive and may be past `idx` when the call is wrapped.
    """
    text = lines[idx]
    m = re.search(r"simp\s*only\s*\[", text)
    if not m:
        if re.search(r"\bsimp\b", text):
            sys.exit(
                f"error: line {idx + 1} is a plain `simp`, not a `simp only [...]`:\n"
                f"  {text.rstrip()}\n"
                "Minimising the explicit args of a plain `simp` proves nothing, because\n"
                "it still draws on the whole default simp set. Change it to `simp?`,\n"
                "compile the file, paste the suggested `simp only [...]` in, then re-run."
            )
        sys.exit(f"error: line {idx + 1} is not a simp call:\n  {text.rstrip()}")
    depth, j, end_line, end_col = 0, m.end() - 1, None, None
    line_no = idx
    buf = []
    while line_no < len(lines):
        row = lines[line_no]
        while j < len(row):
            ch = row[j]
            if ch == "[":
                depth += 1
                if depth == 1:
                    j += 1
                    continue
            elif ch == "]":
                depth -= 1
                if depth == 0:
                    end_line, end_col = line_no, j
                    break
            buf.append(ch)
            j += 1
        if end_line is not None:
            break
        line_no += 1
        j = 0
    if end_line is None:
        sys.exit(f"error: unterminated `[` in simp call at line {idx + 1}")
    args = [a.strip() for a in "".join(buf).split(",") if a.strip()]
    return end_line + 1, args, m.start(), end_col


def render(lines, start, end, simp_idx, simp_span_end, indent_col, args, suffix):
    """Re-emit the declaration with `args` as the simp list and a renamed head."""
    out = []
    for i in range(start, end):
        if i == simp_idx:
            pad = " " * indent_col
            out.append(f"{pad}simp only [{', '.join(args)}]\n" if args
                       else f"{pad}skip\n")
        elif simp_idx < i < simp_span_end:
            continue  # swallowed by the rewritten simp line
        elif i == start and suffix:
            out.append(re.sub(r"\b(theorem|lemma)\s+(\S+)",
                              rf"\1 \2{suffix}", lines[i], count=1))
        else:
            out.append(lines[i])
    return "".join(out)


def compile_lean(path):
    res = subprocess.run(["lake", "env", "lean", path],
                         capture_output=True, text=True)
    return res.stdout + res.stderr


def error_lines(output, path):
    base = os.path.basename(path)
    hits = set()
    for m in re.finditer(r"^\S*%s:(\d+):\d+: error:" % re.escape(base),
                         output, re.MULTILINE):
        hits.add(int(m.group(1)))
    return hits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("line", type=int, help="1-indexed line of the simp call")
    ap.add_argument("--keep", help="comma-separated lemmas; verify just this set")
    args_cli = ap.parse_args()

    with open(args_cli.file) as f:
        lines = f.readlines()
    idx = args_cli.line - 1
    if not 0 <= idx < len(lines):
        sys.exit(f"error: {args_cli.file} has no line {args_cli.line}")

    simp_span_end, simp_args, indent_col, _ = parse_simp(lines, idx)
    start, end = find_decl(lines, idx)
    prefix = "".join(lines[:start])

    scratch = os.environ.get("CLAUDE_SCRATCH", tempfile.gettempdir())
    os.makedirs(scratch, exist_ok=True)
    out_path = os.path.join(scratch, "minimise_simp_probe.lean")

    if args_cli.keep is not None:
        keep = [a.strip() for a in args_cli.keep.split(",") if a.strip()]
        body = render(lines, start, end, idx, simp_span_end, indent_col, keep, "")
        header = prefix + "set_option linter.unusedSimpArgs true\n"
        with open(out_path, "w") as f:
            f.write(header + body)
        output = compile_lean(out_path)
        # Ignore anything the untouched prefix reports; only the variant matters.
        body_start = header.count("\n") + 1
        bad = {b for b in error_lines(output, out_path) if b >= body_start}
        if bad:
            print(f"FAIL: {len(keep)} lemma(s) are not enough.\n")
            print(output.strip())
            return 1
        print(f"OK: proof compiles with {len(keep)} lemma(s):")
        for a in keep:
            print(f"  {a}")
        if "unused" in output:
            print("\nLinter still reports unused args:\n" + output.strip())
        return 0

    chunks = [prefix, "set_option linter.unusedSimpArgs false\n"]
    marks = []  # (line number of the `-- DROP` marker, lemma)
    cursor = prefix.count("\n") + 1
    for i, dropped in enumerate(simp_args):
        keep = [a for a in simp_args if a != dropped]
        header = f"-- DROP {dropped}\n"
        body = render(lines, start, end, idx, simp_span_end, indent_col, keep, f"_v{i}")
        chunks.append(header + body)
        marks.append((cursor, dropped, cursor + 1 + body.count("\n")))
        cursor += 1 + body.count("\n")

    with open(out_path, "w") as f:
        f.write("".join(chunks))

    output = compile_lean(out_path)
    bad = error_lines(output, out_path)

    removable, needed = [], []
    for lo, lemma, hi in marks:
        (needed if any(lo <= b < hi for b in bad) else removable).append(lemma)

    print(f"{len(simp_args)} lemmas tested in one compile ({out_path})\n")
    print(f"LOAD-BEARING ({len(needed)}) — dropping any one breaks the proof:")
    for a in needed:
        print(f"  {a}")
    print(f"\nINDIVIDUALLY REMOVABLE ({len(removable)}):")
    for a in removable:
        print(f"  {a}")
    if removable:
        print("\nNext: removals may interact, so confirm the survivors together:")
        print(f"  python3 {sys.argv[0]} {args_cli.file} {args_cli.line} \\\n"
              f"    --keep {','.join(needed)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
