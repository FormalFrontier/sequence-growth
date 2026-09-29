/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

import SequenceGrowth.Data.Nat.DivisionGrowth
public import Mathlib.Logic.Function.Iterate

set_option warningAsError true

@[expose] public section

namespace SequenceGrowthTest.NatDivisionGrowth

/-- The native iterate of natural division followed by multiplication is a
client of the lower-recurrence theorem. -/
theorem iterate_growth (s n b initial : ℕ) (hs : 0 < s) (hb : 0 < b)
    (hsbn : s * b < n) (hseed : n * (s - 1) < (n - s) * initial) (K : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M,
      K * b ^ m < (fun value : ℕ => n * (value / s))^[m] initial := by
  exact Nat.DivisionGrowth.eventually_dominates
    (fun m => (fun value : ℕ => n * (value / s))^[m] initial)
    s n b hs hb hsbn (by simpa using hseed)
    (by
      intro m
      rw [Function.iterate_succ_apply']) K

/-- Adding a positive surplus at each step makes the recurrence a genuine
lower bound rather than the equality case. -/
theorem surplus_iterate_growth (s n b initial : ℕ) (hs : 0 < s) (hb : 0 < b)
    (hsbn : s * b < n) (hseed : n * (s - 1) < (n - s) * initial) (K : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M,
      K * b ^ m < (fun value : ℕ => n * (value / s) + 1)^[m] initial := by
  exact Nat.DivisionGrowth.eventually_dominates
    (fun m => (fun value : ℕ => n * (value / s) + 1)^[m] initial)
    s n b hs hb hsbn (by simpa using hseed)
    (by
      intro m
      rw [Function.iterate_succ_apply']
      omega) K

/-- Both unit divisor and unit comparison base are supported. -/
theorem unit_divisor_unit_base (u : ℕ → ℕ) (hinit : 0 < u 0)
    (hstep : ∀ m, 2 * (u m / 1) ≤ u (m + 1)) (K : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, K * 1 ^ m < u m := by
  exact Nat.DivisionGrowth.eventually_dominates u 1 2 1
    (by decide) (by decide) (by decide) (by simpa using hinit) hstep K

/-- The constant recurrence satisfies the lower step but not the seed, and
cannot dominate the comparison base even when that base is one. -/
theorem constant_boundary :
    (∀ m : ℕ, 4 * ((fun _ : ℕ => 4) m / 3) ≤ (fun _ : ℕ => 4) (m + 1)) ∧
      ¬ (4 * (3 - 1) < (4 - 3) * 4) ∧
      ¬ (∀ K : ℕ, ∃ M : ℕ, ∀ m ≥ M, K * 1 ^ m < (fun _ : ℕ => 4) m) := by
  refine ⟨by intro m; norm_num, by decide, ?_⟩
  intro h
  obtain ⟨M, hM⟩ := h 4
  have := hM M le_rfl
  norm_num at this

/-- A zero seed gives a zero iterate and fails strict domination even for
`K = 0`. -/
theorem zero_seed_boundary :
    (∀ m : ℕ, 2 * ((fun _ : ℕ => 0) m / 1) ≤ (fun _ : ℕ => 0) (m + 1)) ∧
      ¬ (∀ K : ℕ, ∃ M : ℕ, ∀ m ≥ M, K * 1 ^ m < (fun _ : ℕ => 0) m) := by
  refine ⟨by intro m; norm_num, ?_⟩
  intro h
  obtain ⟨M, hM⟩ := h 0
  have := hM M le_rfl
  norm_num at this

end SequenceGrowthTest.NatDivisionGrowth
