# Sequence Growth

Authors: Formal Frontier Agents

Reusable Lean bounds for sequences of natural numbers whose next term is at least
`n * (u m / s)`. The quotient is **natural division before multiplication**; the
recurrence permits nonnegative surplus and requires no monotonicity assumption.

## Headline results

- [`Nat.DivisionGrowth.affine_lower_bound`](SequenceGrowth/Data/Nat/DivisionGrowth.lean): if `0 < s < n` and
  `∀ m, n * (u m / s) ≤ u (m + 1)`, then for every `m : ℕ`, with
  `λ = (n : ℚ) / s` and `C = (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)`,
  `λ ^ m * ((u 0 : ℚ) - C) + C ≤ (u m : ℚ)`. There is **no** seed condition.
- [`Nat.DivisionGrowth.eventually_dominates`](SequenceGrowth/Data/Nat/DivisionGrowth.lean): under the same recurrence,
  `0 < s`, `0 < b`, `s * b < n`, and the sufficient natural seed
  `n * (s - 1) < (n - s) * u 0`, for **each** `K : ℕ` there is `M : ℕ`
  such that **every** `m ≥ M` satisfies `K * b ^ m < u m`.

The seed is sufficient, not necessary. See [the mathematical guide](docs/DivisionGrowth.md)
for the precise Lean signatures, the rational shift, examples and boundary cases.

## Use

Import `SequenceGrowth` for the whole public library, or import just
`SequenceGrowth.Data.Nat.DivisionGrowth`. For example:

```lean
import SequenceGrowth.Data.Nat.DivisionGrowth

example (u : ℕ → ℕ) (hseed : 2 * (1 - 1) < (2 - 1) * u 0)
    (hstep : ∀ m, 2 * (u m / 1) ≤ u (m + 1)) (K : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, K * 1 ^ m < u m := by
  exact Nat.DivisionGrowth.eventually_dominates u 1 2 1
    (by decide) (by decide) (by decide) hseed hstep K
```

The separate `SequenceGrowthTest` root checks ordinary-import clients, native
iterates (with and without positive surplus), and seed boundary cases.

## Reproduce

The project pins Lean `leanprover/lean4:v4.34.0-rc2`, mathlib commit
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and transitive dependencies
in `lake-manifest.json`. From the repository root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build SequenceGrowth SequenceGrowthTest
```

Fetch the matching mathlib cache **before** building. The source code and
documentation are Apache-2.0 licensed (see `LICENSE`).

## Expected build cost

In one worker checkout with the pinned toolchain, installing Lean took 14 seconds
and fetching/decompressing the matching mathlib cache took 95 seconds (8,892
files). An **incremental**, warning-fatal build of both roots took 5 seconds
(3,092 Lake jobs); that checkout reused cached mathlib and already-built producer
outputs. These are measured intervals for that workload, **not** cold-build
benchmarks. For a fresh checkout, allow at least several minutes as a planning
estimate; download speed, cache availability and local build costs can vary.
Peak memory was not measured.

The Formal Frontier
source-maintainer team shares responsibility for this library; Beacon is the
responsible maintainer for this contribution. Original Lean proofs were authored
by Formal Frontier Agents (formalization-worker-a); this destination transfer
was prepared by Formal Frontier Agents (formalization-worker-b). A previous
independent donor review does not substitute for destination review, checks or
official publication. The destination code has since received independent review
and an applicable build/standard-axiom audit; first-release review, CI pilot,
onboarding and verified publication remain separate steps. This library does not
claim complete formalization of an external source.
