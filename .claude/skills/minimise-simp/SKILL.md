---
name: minimise-simp
description: Replace a `simp` in a Lean proof with a minimal `simp only [...]`. Use when asked to make a proof robust, deterministic, or faster to elaborate, or to tighten, minimise, or pin down a simp call. Most urgent for a *non-terminal* `simp` (one whose goal a later tactic consumes), worthwhile for a terminal one too when the minimal list comes out short.
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

## First: terminal or not?

Two questions decide what to do, and they are independent:

1. **Is the `simp` non-terminal** — does a later tactic consume the goal it
   leaves? That sets how *urgent* this is.
2. **How long is the minimal list** once you have it? That sets whether
   `simp only` is the right answer at all.

|                  | short minimal set (≲ a dozen)      | long minimal set                          |
|------------------|------------------------------------|-------------------------------------------|
| **non-terminal** | apply `simp only` — **do this**    | restructure: `have` / `suffices` / helper |
| **terminal**     | apply `simp only` — nice to have   | leave the `simp` alone                    |

**Non-terminal is the case that actually bites.** A mathlib bump changes what
`simp` does, the goal comes out a different shape, and the tactics after it
break:

> The behaviour of `simp` changes over time as `simp` lemmas are added to (or
> removed from) the library. This means that proofs that use `simp` can break,
> and, unless you know how the set of `simp` lemmas has changed, it can be
> difficult to fix a proof. […] it is easier to maintain Lean code when every
> `simp` closes a goal completely.
>
> — [mathlib docs: non-terminal simps](https://leanprover-community.github.io/extras/simp.html#non-terminal-simps)

**A terminal `simp` cannot break a later tactic**, because there isn't one — the
worst case is that it stops closing the goal, which is a loud, local failure.
So minimising it is a genuine improvement (deterministic, self-documenting,
faster to elaborate) but never urgent. Do it when the answer comes out short;
don't fight for it.

Note that "terminal" means *closes its own goal*, not *last line of the file*:

```lean
cases b <;> norm_num [h]        -- simp above it is NON-terminal: minimise
cases g 0 <;> simp [h]          -- terminal (closes both branches)
· simp [a, b]                   -- terminal within its bullet
· simp [a, b]                   -- but NON-terminal if norm_cast/rw follow in the bullet
cases f 0 <;> simp [a] <;> ring -- NON-terminal: `ring` consumes simp's output
```

### Restructuring beats a long list

When a **non-terminal** `simp` minimises to something long, `simp only` is the
wrong fix. These make it terminal instead, which is what you actually want:

- `have h : P := by ...; simp` — the `simp` closes the `have`'s goal, and the
  stated `P` pins the shape rather than leaving it to whatever simp produces.
- `suffices h : P by simpa` — when `simp` would reduce the goal to `P`, state
  `P` and let `simpa` close it.
- `simpa using h` — in place of `simp at ⊢ h; exact h`.

A stated intermediate goal documents the proof and survives mathlib changes
better than a 27-lemma list, because the *statement* does the pinning.

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

**If the `simp` sits in a combinator chain** (`cases h <;> simp [...]`, or a `·`
focus block), it runs once per branch and `simp?` prints *one suggestion per
branch*, each different. Paste in the **union** of them — that is the smallest
list guaranteed to cover every branch — then minimise from there. With several
such call sites in a file, convert them to `simp?` one at a time: the
suggestions carry no line numbers, so doing them all at once makes them
impossible to map back.

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

`OK` means done — that is the common case, and it is one compile.

`FAIL` means removals interact: a lemma that was droppable on its own became
necessary once its substitutes went. Rather than iterating by hand, use

```sh
python3 .claude/skills/minimise-simp/scripts/minimise_simp.py <file.lean> <line> --greedy
```

which runs the batch pass and then drops the removable lemmas **cumulatively**,
re-checking after each (one compile per candidate) and keeping any that turn out
to be load-bearing after all. It reports the final list and warns when the
result is too long to be worth applying.

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
- **Know when to walk away.** If a proof is load-bearing on most of a long list,
  stop: leave a terminal `simp` alone, and restructure a non-terminal one. The X-spider proofs in
  `SemanticsTesting/05Spiders.lean` are the worked counter-example: `simp?`
  suggests ~40 lemmas per call site, `--greedy` gets one of them only from 35
  down to 27, and 27 opaque lemma names are plainly worse to read than the
  `simp [zSpiderSem, hadSem, Phase.angle]` they would replace — which at least
  names the three definitional unfoldings actually being done. Roughly: above a
  dozen lemmas, the robustness win no longer pays for the readability loss.
  Report the numbers and recommend restructuring instead — a helper lemma in
  `SemanticsTesting/Utils.lean` that does the unfolding once, or a
  `have h : P := by ...` / `suffices h : P by simpa` that makes the `simp`
  terminal. Any of those beats applying the list.
- A minimisation that only shaves a few lemmas off a long list is telling you
  the simp call is doing real multi-step normalisation, not incidental
  tidying. That is a refactor signal, not a tuning opportunity.

## Manual fallback

If the script cannot parse an unusual declaration, do the same thing by hand:
copy the theorem N times into a scratch file under the scratchpad directory,
prefix each copy with a `-- DROP <lemma>` comment, add
`set_option linter.unusedSimpArgs false` so warnings don't drown the errors,
compile once, and map each reported error line back to the `-- DROP` marker
above it.
