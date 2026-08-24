---
name: minimise-simp
description: Replace a `simp` in a Lean proof with a minimal `simp only [...]`. Use when a proof in this repo closes with a bare `simp`/`norm_num`, when asked to make a proof robust, deterministic, or faster to elaborate, or when asked to tighten, minimise, or pin down a simp call.
---

# Minimising simp calls

A bare `simp` is a liability: it draws on the whole default simp set, so a
mathlib bump can silently change what it does and break the proof — or, worse,
leave a different goal that the following tactics no longer close. Replacing it
with the smallest `simp only [...]` that still works makes the proof
self-documenting, deterministic across mathlib versions, and quicker to
elaborate.

`reference/ClaudeSkill.lean`, next to this file, is the worked example the skill
is drawn from: the same Bell-state theorem proved four times, once per stage of
the loop below, from `simp` down to a three-lemma `simp only`. It is a live
file — check it with

```sh
lake env lean .claude/skills/minimise-simp/reference/ClaudeSkill.lean
```

from the repo root. It sits outside the `SemanticsTesting` library, so `lake
build` does **not** cover it; if a mathlib bump changes the suggested lemma
lists, this file will not fail CI, and the stage-3 and stage-4 lists in it may
drift out of date. Re-run the command above before trusting its exact lemma
names.

## Checking a file

One file, roughly two seconds — do **not** run `lake build`, which also rebuilds
the npm widget bundle:

```sh
lake env lean SemanticsTesting/03ZSpiders.lean
```

This prints everything you need on stdout: `simp?` suggestions as `Try this:`,
errors as `<file>:<line>:<col>: error: ...`, and unused-argument warnings. The
InfoView is not involved, so the whole loop is scriptable.

Note that errors are reported at the position of the declaration's `by`, not at
the offending tactic line.

## The loop

### 1. Get a starting list with `simp?`

Change the `simp` to `simp?`, compile the file, and read the suggestion:

```
Try this:
  [apply] simp only [IsEmpty.forall_iff, Fin.forall_fin_succ, Fin.isValue, ...]
```

Paste that in as `simp only [...]`. It will be long — for the Bell state it is
19 lemmas — and most of it is redundant. `simp?` reports every rewrite that
fired, not every rewrite that mattered.

### 2. Take the free win from the linter

If the file compiles with

```
warning: This simp argument is unused:
  Fin.succ_zero_eq_one
```

delete those arguments immediately. An argument simp never fired cannot affect
the resulting goal, so removing it is always safe and needs no re-check.

This pass is necessary but not sufficient. In the Bell-state example the
19-lemma list produces **no** linter warnings at all — simp genuinely used all
19 — and yet only 3 are needed. The rest fired but did work that the closing
`norm_num` would have done anyway. That is what the next step finds.

### 3. Batch-test every removal in one compile

Do not remove lemmas one at a time and recompile after each. Almost all of the
two seconds is mathlib import time, so N candidate removals cost the same as one
if you put them in a single file. The bundled script does this: it copies the
enclosing declaration N times, drops lemma `i` from copy `i`, and compiles once.

```sh
python3 .claude/skills/minimise-simp/scripts/minimise_simp.py <file.lean> <line-of-simp-only>
```

Pass the 1-indexed line where the `simp only` starts; multi-line calls are
handled. Output:

```
19 lemmas tested in one compile

LOAD-BEARING (3) — dropping any one breaks the proof:
  Fin.forall_fin_succ
  Fin.succ_zero_eq_one
  Matrix.cons_val

INDIVIDUALLY REMOVABLE (16):
  IsEmpty.forall_iff
  ...
```

Set `CLAUDE_SCRATCH` to your scratchpad directory so the probe file lands there
rather than in the system temp dir.

### 4. Confirm the survivors together

Removals are not independent: two lemmas can each be droppable alone yet be
needed as a pair, if each covers for the other. So keeping only the load-bearing
set is a hypothesis, not a result. Verify it:

```sh
python3 .claude/skills/minimise-simp/scripts/minimise_simp.py <file.lean> <line> \
  --keep Fin.forall_fin_succ,Fin.succ_zero_eq_one,Matrix.cons_val
```

`OK` means done. `FAIL` means some interaction is at play — add back the
individually-removable lemmas until it passes, then re-run the batch pass on
that smaller list and iterate. Each round costs one compile.

### 5. Apply and check the real file

Edit the actual `simp only` in the source, then compile the file to confirm.
Expect no errors and no unused-argument warnings.

## Scope and judgement

- Only ever point the script at a `simp only [...]`. Minimising the explicit
  arguments of a plain `simp [a, b]` proves nothing, since it still has the
  default simp set behind it. The script refuses this and tells you to run
  `simp?` first.
- The result is minimal relative to **the whole proof**, not to the simp call in
  isolation. A lemma is dropped when the closing `cases ... <;> norm_num` can
  absorb its work. That is the property worth having.
- Leave `norm_num` and `field_simp` alone. They are simp wrappers, but their
  default sets are the point of using them; a minimal `simp only` is not a
  substitute.
- Don't chase the last lemma at the cost of readability. A four-lemma list that
  names the real reasoning steps beats a three-lemma one held together by an
  accident of rewrite order.
- If a proof is genuinely load-bearing on most of a long list, that is a signal
  the statement wants a helper lemma in `SemanticsTesting/Utils.lean` instead.

## Manual fallback

If the script cannot parse an unusual declaration, do the same thing by hand:
copy the theorem N times into a scratch file under the scratchpad directory,
prefix each copy with a `-- DROP <lemma>` comment, add
`set_option linter.unusedSimpArgs false` so warnings don't drown the errors,
compile once, and map each reported error line back to the `-- DROP` marker
above it.
