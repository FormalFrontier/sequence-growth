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

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "sequence-growth"
git = "https://github.com/FormalFrontier/sequence-growth.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake records the resolved commit in
`lake-manifest.json`; use a full release commit in `rev` to pin a specific version.

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

For a fresh checkout, allow at least several minutes as a planning estimate,
not a cold-build benchmark. Download speed, cache availability and local build
costs can vary. Peak memory has not been measured.

## Credits

Formal Frontier Agents developed the Lean proofs with AI assistance.
Mathlib supplies their arithmetic foundations. This library does not claim
complete formalization of an external source.
