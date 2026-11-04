# A082935 — Wilson's first-round digit-sum conjecture, proved in Lean 4

[![CI](https://github.com/gaudinfrederic/oeis-A082935/actions/workflows/ci.yml/badge.svg)](https://github.com/gaudinfrederic/oeis-A082935/actions/workflows/ci.yml)

Machine-checked proof of the conjecture on
[OEIS A082935](https://oeis.org/A082935) (Meenakshi Srikanth, 2003):
`a(n)` = smallest palindrome whose decimal expansion begins with `n`
and whose iterated digit sum reaches `n` at some stage `k ≥ 1`.
The OEIS records the conjecture (Robert G. Wilson v, Jun 27 2003,
checked to `n = 100`): **except for `n = 19`, the first-round digit
sum itself is `n`; for `n = 19` the first-round sum is `199` and the
second-round sum is `19`** — proved here for every `n ≥ 1`, together
with the **exact formula** (`σ` = decimal digit sum):

- `a(n) = n` for `n ≤ 9`;
- `a(19) = 1949999999999999999999491` — `"194"` + nineteen `9`s +
  `"491"`, with `σ = 199` then `σ² = 19`;
- for `n ≥ 10`, `n ≠ 19` (one proves `n - 2σ(n) ≥ 0`, with equality
  exactly at `n = 18`):
  `a(n) = concat(n, μ(n - 2σ(n)), rev(n))`, where `μ(t)` is the
  shortest palindromic digit-string with digit sum `t` — the empty
  string at `t = 0` — lexicographically smallest among strings of
  that length (the `A062388`-style pattern: leading digit, block of
  nines, symmetric tail). `concat`/`rev` act on decimal digit
  strings, re-evaluated as an integer.

Corollary on the sister sequence
[OEIS A082217](https://oeis.org/A082217) ("smallest palindrome
beginning with `n` and digit sum `n`, or `0` if none exists"):
`a082217(n) = 0` **iff** `n = 19`, and `a082217(n) = a082935(n)`
otherwise — as the comment on that entry already indicated
through the key inequality ("every other integer `k > 9` has
digit sum `≤ k/2`, so the center can always be filled in"),
which settles the existence informally.

## Theorems

```lean
theorem A082935_wilson_conjecture :
    (∀ n : ℕ, 1 ≤ n → n ≠ 19 → sigma10 (a082935 n) = n) ∧
    sigma10 (a082935 19) = 199 ∧
    sigma10^[2] (a082935 19) = 19

theorem A082935_formula :
    (∀ n : ℕ, 1 ≤ n → n ≤ 9 → a082935 n = n) ∧
    a082935 19 = 1949999999999999999999491 ∧
    (∀ n : ℕ, 10 ≤ n → n ≠ 19 →
      let t := n - 2 * sigma10 n
      a082935 n = Nat.ofDigits 10 ((Nat.digits 10 n).reverse ++
        gmid (lmin t) t ++ Nat.digits 10 n))

theorem A082217_characterization {n : ℕ} (hn : 1 ≤ n) :
    (a082217 n = 0 ↔ n = 19) ∧ (n ≠ 19 → a082217 n = a082935 n)
```

`a082935`/`a082217` are `sInf` over the admissible palindromes
(totalizing: `0` on the empty set, which happens exactly at
`n = 19` for `a082217`); `beginsWith10` is `List.IsSuffix` on
little-endian `Nat.digits`; `reachesDigitSum` requires stage
`k ≥ 1`. `lmin t`/`gmid l t` realize the minimal palindromic
middle (`isPalDigitString`).

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `lake env lean A082935.lean` — exit 0, **zero `sorry`**,
  **zero `native_decide`**
- `#print axioms` on all five top theorems —
  `[propext, Classical.choice, Quot.sound]` — the three standard
  axioms only. **No `native_decide`, no `sorryAx`** — fully
  verified within the Lean 4 kernel (all finite certificates,
  including the 25-digit `n = 19` witness, are kernel `decide`).

## Contents

- `A082935.lean` — the development (1371 lines, self-contained:
  `import Mathlib` only, no project dependencies)

## Honesty note

The conjecture was stated by Robert G. Wilson v (2003) in the
comments of OEIS A082935 and checked by him to `n = 100`; the
A082217 comment already records the existence argument
(digit sum `≤ k/2` for `k > 9`, `k ≠ 19`), which settles the
existence informally. To our knowledge this repository provides
the **first complete written proof** — exact formula and
minimality across stages included — and the **first
formalization**; the conjectured phenomenon itself is not
claimed as new. The formalization of the raw
OEIS text was audited blindly by an independent oracle (verbatim
exchange archived in the package under `VERIFICATIONS/`).

## Reproduce

```sh
lake build        # installs toolchain via elan, fetches mathlib cache
lake env lean A082935.lean
```

## Reference

Sibling: *Prescribed digit sums in residue classes and a
conjecture of Murthy (OEIS A077754)*, F. Gaudin —
https://doi.org/10.5281/zenodo.23879088
