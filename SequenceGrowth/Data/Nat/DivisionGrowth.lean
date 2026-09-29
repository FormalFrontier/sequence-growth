/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic

/-!
# Growth from a lower natural-division recurrence

A lower bound on `n * (u m / s)` yields a rational affine bound on `u m` and,
under a sufficient initial threshold, strict eventual domination of `K * b ^ m`.
The division in the recurrence is natural division and precedes multiplication.
-/

set_option warningAsError true

@[expose] public section

namespace Nat.DivisionGrowth

private theorem step_bound (u : ℕ → ℕ) (s n : ℕ) (hs : 0 < s)
    (hstep : ∀ m, n * (u m / s) ≤ u (m + 1)) (m : ℕ) :
    (n : ℚ) * (u m : ℚ) ≤ (s : ℚ) * (u (m + 1) : ℚ) +
      (n : ℚ) * ((s - 1 : ℕ) : ℚ) := by
  have hrem : u m % s ≤ s - 1 := by
    have := Nat.mod_lt (u m) hs
    omega
  have hmul : n * (u m % s) ≤ n * (s - 1) := Nat.mul_le_mul_left n hrem
  have hquot : n * (s * (u m / s)) ≤ s * u (m + 1) := by
    calc
      _ = s * (n * (u m / s)) := by ring
      _ ≤ s * u (m + 1) := Nat.mul_le_mul_left s (hstep m)
  have hnat : n * u m ≤ s * u (m + 1) + n * (s - 1) := by
    calc
      n * u m = n * (u m % s) + n * (s * (u m / s)) := by
        conv_lhs => rw [← Nat.mod_add_div (u m) s]
        ring
      _ ≤ n * (s - 1) + s * u (m + 1) := Nat.add_le_add hmul hquot
      _ = _ := by omega
  exact_mod_cast hnat

private theorem affine_step (u : ℕ → ℕ) (s n : ℕ) (hs : 0 < s) (hsn : s < n)
    (hstep : ∀ m, n * (u m / s) ≤ u (m + 1)) (m : ℕ) :
    ((n : ℚ) / s) * ((u m : ℚ) -
      (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)) +
      (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s) ≤ (u (m + 1) : ℚ) := by
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hsnQ : (s : ℚ) < n := by exact_mod_cast hsn
  have hdiff : (0 : ℚ) < (n : ℚ) - s := sub_pos.mpr hsnQ
  let offset : ℚ := (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)
  have hoffset : ((n : ℚ) / s - 1) * offset =
      ((n : ℚ) / s) * ((s - 1 : ℕ) : ℚ) := by
    dsimp [offset]
    field_simp
  have hnat := step_bound u s n hs hstep m
  have hlinear : ((n : ℚ) / s) * (u m : ℚ) -
      ((n : ℚ) / s) * ((s - 1 : ℕ) : ℚ) ≤ (u (m + 1) : ℚ) := by
    calc
      _ = ((n : ℚ) * (u m : ℚ) - (n : ℚ) * ((s - 1 : ℕ) : ℚ)) / s := by ring
      _ ≤ (u (m + 1) : ℚ) := (div_le_iff₀ hsQ).2 (by linarith)
  change ((n : ℚ) / s) * ((u m : ℚ) - offset) + offset ≤ _
  linear_combination hlinear - hoffset

/-- Every lower recurrence `n * (u m / s) ≤ u (m + 1)` has a rational affine
lower bound. The shift can be larger than the initial value; no seed condition
is needed for this finite estimate. -/
theorem affine_lower_bound (u : ℕ → ℕ) (s n : ℕ) (hs : 0 < s) (hsn : s < n)
    (hstep : ∀ m, n * (u m / s) ≤ u (m + 1)) (m : ℕ) :
    ((n : ℚ) / s) ^ m * ((u 0 : ℚ) -
      (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)) +
      (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s) ≤ (u m : ℚ) := by
  let ratio : ℚ := (n : ℚ) / s
  let offset : ℚ := (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)
  have hratio : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hstepQ (i : ℕ) : ratio * ((u i : ℚ) - offset) + offset ≤
      (u (i + 1) : ℚ) := affine_step u s n hs hsn hstep i
  change ratio ^ m * ((u 0 : ℚ) - offset) + offset ≤ (u m : ℚ)
  induction m with
  | zero => simp
  | succ i hi =>
      calc
        ratio ^ (i + 1) * ((u 0 : ℚ) - offset) + offset =
            ratio * (ratio ^ i * ((u 0 : ℚ) - offset) + offset - offset) +
              offset := by rw [pow_succ]; ring
        _ ≤ ratio * ((u i : ℚ) - offset) + offset := by
          apply add_le_add_left
          exact mul_le_mul_of_nonneg_left (sub_le_sub_right hi offset) hratio
        _ ≤ (u (i + 1) : ℚ) := hstepQ i

/-- A sufficient natural seed condition makes a natural-division lower
recurrence eventually strictly dominate every fixed multiple of `b ^ m`,
uniformly at all indices beyond a threshold. -/
theorem eventually_dominates (u : ℕ → ℕ) (s n b : ℕ) (hs : 0 < s) (hb : 0 < b)
    (hsbn : s * b < n) (hseed : n * (s - 1) < (n - s) * u 0)
    (hstep : ∀ m, n * (u m / s) ≤ u (m + 1)) (K : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, K * b ^ m < u m := by
  have hsn : s < n := by nlinarith
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hsnQ : (s : ℚ) < n := by exact_mod_cast hsn
  have hdiff : (0 : ℚ) < (n : ℚ) - s := sub_pos.mpr hsnQ
  let offset : ℚ := (n : ℚ) * ((s - 1 : ℕ) : ℚ) / ((n : ℚ) - s)
  let delta : ℚ := (u 0 : ℚ) - offset
  let ratio : ℚ := (n : ℚ) / ((s : ℚ) * b)
  have hoffset : 0 ≤ offset := by dsimp [offset]; positivity
  have hseedQ : (n : ℚ) * ((s - 1 : ℕ) : ℚ) <
      ((n : ℚ) - s) * (u 0 : ℚ) := by
    have h := (Nat.cast_lt (α := ℚ)).2 hseed
    norm_num only [Nat.cast_mul, Nat.cast_sub hsn.le] at h
    exact h
  have hdelta : 0 < delta := by
    dsimp [delta, offset]
    rw [sub_pos, div_lt_iff₀ hdiff]
    simpa [mul_comm] using hseedQ
  have hsbnQ : (s : ℚ) * b < (n : ℚ) := by exact_mod_cast hsbn
  have hratio : 1 < ratio := by
    dsimp [ratio]
    exact (one_lt_div₀ (mul_pos hsQ hbQ)).2 (by simpa using hsbnQ)
  have hfactor : ratio * (b : ℚ) = (n : ℚ) / s := by
    dsimp [ratio]
    field_simp
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt ((K : ℚ) / delta) hratio
  refine ⟨M, ?_⟩
  intro m hm
  have hpow : ((K : ℚ) / delta) < ratio ^ m :=
    lt_of_lt_of_le hM (pow_right_mono₀ hratio.le hm)
  have hK : (K : ℚ) < delta * ratio ^ m := by
    simpa [mul_comm] using (div_lt_iff₀ hdelta).1 hpow
  have hscaled : (K : ℚ) * (b : ℚ) ^ m <
      ((n : ℚ) / s) ^ m * delta := by
    calc
      (K : ℚ) * (b : ℚ) ^ m < (delta * ratio ^ m) * (b : ℚ) ^ m :=
        mul_lt_mul_of_pos_right hK (pow_pos hbQ m)
      _ = delta * (ratio * (b : ℚ)) ^ m := by rw [mul_pow]; ring
      _ = ((n : ℚ) / s) ^ m * delta := by rw [hfactor]; ring
  have hfinite := affine_lower_bound u s n hs hsn hstep m
  have hcast : (K : ℚ) * (b : ℚ) ^ m < (u m : ℚ) := by
    dsimp [delta, offset] at hscaled
    linarith
  exact_mod_cast hcast

end Nat.DivisionGrowth
