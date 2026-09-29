# Natural-division lower recurrences

Import `SequenceGrowth.Data.Nat.DivisionGrowth` (or the public root
`SequenceGrowth`). In the public namespace `Nat.DivisionGrowth`, both results
work with *any* `u : ℕ → ℕ` satisfying

```lean
hstep : ∀ m, n * (u m / s) ≤ u (m + 1)
```

The quotient is natural division, taken **before** multiplication by `n`.
The next term can exceed that product, and `u` need not be monotone.

## Exact results

`affine_lower_bound u s n hs hsn hstep m` requires `0 < s`, `s < n` and
the displayed step condition. Write `λ = (n : ℚ) / s` and
`C = (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)`. Its conclusion for every
natural `m` is

```text
λ ^ m * ((u 0 : ℚ) - C) + C ≤ (u m : ℚ).
```

Subtraction in `(u 0 : ℚ) - C` is *rational*, not truncated natural
subtraction; the bound holds even if the shifted initial value is nonpositive.

`eventually_dominates u s n b hs hb hsbn hseed hstep K` additionally
requires `0 < b`, `s * b < n` and the sufficient **natural** seed
`n * (s - 1) < (n - s) * u 0`. It produces `M : ℕ` such that
`∀ m ≥ M, K * b ^ m < u m`. The threshold may depend on `K`, but **every**
later index satisfies the strict inequality. The seed is sufficient, not
claimed necessary; `s = 1`, `b = 1` and `K = 0` are supported.

Natural division yields `u m % s ≤ s - 1`. Casting the one-step estimate to
`ℚ` and using `(λ - 1) * C = λ * (s - 1)` gives the rational affine recurrence.
Induction proves the first theorem. With the seed, `u 0 - C > 0`; with
`s * b < n`, `λ / b > 1`. Unbounded rational powers and monotonicity give the
uniform strict tail. The proof uses existing mathlib arithmetic rather than a
floor-valued real sequence or a topology assumption.

## Clients and boundaries

`SequenceGrowthTest.Data.Nat.DivisionGrowth` uses an *ordinary import* of the
producer; it applies the results to native iterates of
`x ↦ n * (x / s)` and `x ↦ n * (x / s) + 1`, the latter with a genuine
positive surplus. Its other examples test the unit divisor/base and show that
a constant lower recurrence without the seed need not dominate even the unit
base, while a zero seed cannot strictly dominate even at `K = 0`.

This is a standalone numerical-sequence API. It does not make a claim about a
particular source's notation, special predicates or full source coverage.
