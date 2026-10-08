/-
Copyright (c) 2026 Radu Irbe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Radu Irbe
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cesàro means of geometrically decaying sequences

For a normed-space-valued sequence `a` with `‖a k‖ ≤ C * r ^ k` and `0 ≤ r < 1`, the Cesàro
means `n⁻¹ • ∑ k < n, a k` tend to zero.  The file gives the explicit rate bound first
(`norm_sum_range_smul_le_of_norm_le_geometric`, independently useful), then the limit; the
real-valued special cases are kept under their original names as corollaries.
-/

@[expose] public section

open Filter

/-- **Explicit rate for Cesàro means of a geometrically dominated sequence**: if
`‖a k‖ ≤ C * r ^ k` with `0 ≤ C` and `0 ≤ r < 1`, then for every `n ≥ 1` the norm of the
`n`-th Cesàro mean of `a` is bounded by `(C / (1 - r)) * n⁻¹`. -/
theorem norm_sum_range_smul_le_of_norm_le_geometric {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {a : ℕ → E} {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, ‖a k‖ ≤ C * r ^ k) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, a k‖ ≤ (C / (1 - r)) * (n : ℝ)⁻¹ := by
  have hden : 0 < 1 - r := by linarith
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  calc ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, a k‖
      = (n : ℝ)⁻¹ * ‖∑ k ∈ Finset.range n, a k‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ‖a k‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _)
          (le_of_lt (inv_pos.mpr hnpos))
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, C * r ^ k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => h k)
          (le_of_lt (inv_pos.mpr hnpos))
    _ = C * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, r ^ k) := by
        simp only [Finset.mul_sum]
        ring
    _ ≤ C * ((n : ℝ)⁻¹ * (1 / (1 - r))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hnpos))
        rw [le_div_iff₀ hden, geom_sum_mul_neg]
        linarith [pow_nonneg hr0 n]
    _ = (C / (1 - r)) * (n : ℝ)⁻¹ := by ring

/-- **Cesàro means of a geometrically dominated sequence tend to zero**: if
`‖a k‖ ≤ C * r ^ k` with `0 ≤ C` and `0 ≤ r < 1`, then
`n⁻¹ • ∑ k < n, a k → 0`, by squeezing with the explicit rate
`(C / (1 - r)) * n⁻¹`. -/
theorem tendsto_sum_range_smul_nhds_zero_of_norm_le_geometric {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℕ → E} {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (h : ∀ k, ‖a k‖ ≤ C * r ^ k) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, a k) atTop (nhds 0) := by
  have hb0 : Tendsto (fun n : ℕ ↦ (C / (1 - r)) * (n : ℝ)⁻¹) atTop (nhds 0) := by
    have hninv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := C / (1 - r))).mul hninv
  have hle : ∀ n : ℕ,
      ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, a k‖ ≤ (C / (1 - r)) * (n : ℝ)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact norm_sum_range_smul_le_of_norm_le_geometric hC hr0 hr1 h hn
  have hnorm0 : Tendsto
      (fun n : ℕ ↦ ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, a k‖) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) hb0
      (fun n => norm_nonneg _) hle
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hlt : ∀ᶠ n : ℕ in atTop, (C / (1 - r)) * (n : ℝ)⁻¹ < ε := by
    have h := tendsto_def.mp hb0 (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
    filter_upwards [h] with n hn
    change (C / (1 - r)) * (n : ℝ)⁻¹ ∈ Metric.ball 0 ε at hn
    have hnn : 0 ≤ (C / (1 - r)) * (n : ℝ)⁻¹ := by
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · simp
      · positivity
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hn
    exact hn
  filter_upwards [eventually_atTop.2 ⟨0, fun n _ => hle n⟩, hlt] with n hn hlt'
  rw [dist_zero_right]
  exact lt_of_le_of_lt hn hlt'

theorem abs_sum_range_div_le_of_abs_le_geometric {a : ℕ → ℝ} {C r : ℝ} (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, |a k| ≤ C * r ^ k) {n : ℕ} (hn : 1 ≤ n) :
    |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k| ≤ (C / (1 - r)) * (n : ℝ)⁻¹ := by
  have h' : ∀ k : ℕ, ‖a k‖ ≤ C * r ^ k := fun k => by
    rw [Real.norm_eq_abs]
    exact h k
  have hgen : ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, a k‖
      ≤ (C / (1 - r)) * (n : ℝ)⁻¹ :=
    norm_sum_range_smul_le_of_norm_le_geometric hC hr0 hr1 h' hn
  rwa [Real.norm_eq_abs, smul_eq_mul] at hgen

/-- Real-valued special case of
`tendsto_sum_range_smul_nhds_zero_of_norm_le_geometric`. -/
theorem tendsto_sum_range_div_nhds_zero_of_abs_le_geometric {a : ℕ → ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, |a k| ≤ C * r ^ k) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k) atTop (nhds 0) := by
  have hgen : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, a k) atTop
      (nhds 0) :=
    tendsto_sum_range_smul_nhds_zero_of_norm_le_geometric hC hr0 hr1
      (fun k => by
        rw [Real.norm_eq_abs]
        exact h k)
  refine hgen.congr' ?_
  filter_upwards with n
  simp [smul_eq_mul]
