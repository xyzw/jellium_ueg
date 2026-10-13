import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Scalar checks for the upper comparison in `jellium_ueg.tex`.

These theorems check the arithmetic of the collar coefficient, the surface
estimate, and the final error bound. The existence of the trial states and the
analytic estimates for their energies are explicit hypotheses where used.
This file does not assert that those analytic estimates have been formalized.
-/

namespace Jellium.Upper

/-- The bounds on the two radial integrals imply the stated uniform bounds
on their ratio, as in the compensated collar construction. -/
theorem collar_coefficient_bounds
    {r b numerator denominator : ℝ}
    (hr : 0 < r) (hb : 0 < b)
    (hnum_lower : r ^ 2 / 4 ≤ numerator)
    (hnum_upper : numerator ≤ 9 * r ^ 2 / 4)
    (hden_lower : r ^ 2 * b ≤ denominator)
    (hden_upper : denominator ≤ 4 * r ^ 2 * b) :
    1 / (16 * b) ≤ numerator / denominator ∧
      numerator / denominator ≤ 9 / (4 * b) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hd : 0 < denominator := lt_of_lt_of_le (mul_pos hr2 hb) hden_lower
  constructor
  · apply (le_div_iff₀ hd).2
    have h : denominator / (16 * b) ≤ r ^ 2 / 4 := by
      apply (div_le_iff₀ (by positivity : 0 < 16 * b)).2
      nlinarith
    calc
      1 / (16 * b) * denominator = denominator / (16 * b) := by ring
      _ ≤ r ^ 2 / 4 := h
      _ ≤ numerator := hnum_lower
  · apply (div_le_iff₀ hd).2
    have h : 9 * r ^ 2 / 4 ≤ 9 / (4 * b) * denominator := by
      have h' : 9 * r ^ 2 / 4 ≤ (9 * denominator) / (4 * b) := by
        apply (le_div_iff₀ (by positivity : 0 < 4 * b)).2
        nlinarith
      convert h' using 1
      ring
    exact le_trans hnum_upper h

/-- Choosing the compensating amplitude as the missing mass divided by the
added profile's mass makes the total correction exactly neutral. -/
theorem collar_mass_correction
    {missingMass profileMass : ℝ} (hprofile : profileMass ≠ 0) :
    -missingMass + (missingMass / profileMass) * profileMass = 0 := by
  field_simp
  ring

/-- The geometric surface bound used for every finite packing. Here
`volumeFactor` is the positive constant `4 * π / 3`. -/
theorem surface_bound
    {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    {rmin volumeFactor : ℝ} (hrmin : 0 < rmin)
    (hvolume : 0 < volumeFactor)
    (hr : ∀ i ∈ s, rmin ≤ r i) :
    (∑ i ∈ s, r i ^ 2) ≤
      (∑ i ∈ s, volumeFactor * r i ^ 3) / (volumeFactor * rmin) := by
  apply (le_div_iff₀ (mul_pos hvolume hrmin)).2
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hri : 0 ≤ r i := le_trans (le_of_lt hrmin) (hr i hi)
  have hmul := mul_le_mul_of_nonneg_left (hr i hi) (sq_nonneg (r i))
  nlinarith [mul_nonneg (le_of_lt hvolume)
    (show 0 ≤ r i ^ 3 - r i ^ 2 * rmin by nlinarith)]

/-- The inner-cube polynomial estimate in the explicit counting claim. -/
theorem inner_cube_volume_bound {R t : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) :
    R ^ 3 - 3 * t * R ^ 2 ≤ (R - t) ^ 3 := by
  have hfactor : 0 ≤ 3 * R - t := by linarith
  nlinarith [mul_nonneg (sq_nonneg t) hfactor]

/-- The outer-cube polynomial estimate with the manuscript's constant 26. -/
theorem outer_cube_volume_bound {R L : ℝ} (hL : 0 ≤ L) (hLR : L ≤ R) :
    (R + 2 * L) ^ 3 ≤ R ^ 3 + 26 * L * R ^ 2 := by
  have hR : 0 ≤ R := hL.trans hLR
  have hsq : L ^ 2 ≤ R ^ 2 := by nlinarith
  have hthird : L ^ 3 ≤ L * R ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hL]
  have hmiddle : L ^ 2 * R ≤ L * R ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hL hR) (sub_nonneg.mpr hLR)]
  nlinarith

/-- Arithmetic of the uniform counting claim once the inner and outer cell
volume comparisons have been established. The actual upper-comparison chain
instead proves an exact translation-average formula in `UpperCoverage`. -/
theorem counting_error_of_cell_bounds {R L δ θ V : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hR : 2 * (δ + L) ≤ R)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlower : θ * (R - 2 * (δ + L)) ^ 3 ≤ V)
    (hupper : V ≤ θ * (R + 2 * L) ^ 3) :
    |V - θ * R ^ 3| ≤ 26 * (δ + L) * R ^ 2 := by
  have hinner := inner_cube_volume_bound (show 0 ≤ 2 * (δ + L) by positivity) hR
  have houter := outer_cube_volume_bound hL (show L ≤ R by linarith)
  have hlow := mul_le_mul_of_nonneg_left hinner hθ0
  have hupp := mul_le_mul_of_nonneg_left houter hθ0
  have hsmall : θ * (6 * (δ + L) * R ^ 2) ≤ 6 * (δ + L) * R ^ 2 := by
    exact mul_le_of_le_one_left (by positivity) hθ1
  have hlarge : θ * (26 * L * R ^ 2) ≤ 26 * L * R ^ 2 := by
    exact mul_le_of_le_one_left (by positivity) hθ1
  have hδR : 0 ≤ δ * R ^ 2 := mul_nonneg hδ (sq_nonneg R)
  have hLR : 0 ≤ L * R ^ 2 := mul_nonneg hL (sq_nonneg R)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The last finite-error inequality does not require the Jellium energy
`e` to have a prescribed sign. The parameter `c` represents the collar error. -/
theorem quantitative_error
    {e ε θ K₀ c : ℝ}
    (hε : 0 ≤ ε) (hθ_lower : 1 - ε ≤ θ) (hθ_upper : θ ≤ 1)
    (hK₀ : 0 ≤ K₀) :
    θ * (e + ε) + K₀ * (1 - θ) + c ≤
      e + ε * (1 + max (-e) 0 + K₀) + c := by
  have hgap : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_upper
  have hgap_upper : 1 - θ ≤ ε := by linarith
  have hconstant : 0 ≤ max (-e) 0 + K₀ := by positivity
  have henergy : K₀ - e ≤ max (-e) 0 + K₀ := by
    linarith [le_max_left (-e) 0]
  have hθeps := mul_le_mul_of_nonneg_right hθ_upper hε
  calc
    θ * (e + ε) + K₀ * (1 - θ) + c =
        e + θ * ε + (1 - θ) * (K₀ - e) + c := by ring
    _ ≤ e + ε + (1 - θ) * (max (-e) 0 + K₀) + c := by
      gcongr
      linarith
    _ ≤ e + ε + ε * (max (-e) 0 + K₀) + c := by
      gcongr
    _ = _ := by ring

/-- Conditional completion of the upper comparison. The trial-state bound is
the hypothesis `htrial`, not a literature theorem or an axiom. Its parameters
may depend on `ε`, matching the order of limits in the manuscript. -/
theorem upper_le_of_trial_bounds
    {E e K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (htrial : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ θ c : ℝ, 1 - ε ≤ θ ∧ θ ≤ 1 ∧ c ≤ ε ∧
        E ≤ θ * (e + ε) + K₀ * (1 - θ) + c) :
    E ≤ e := by
  by_contra hnot
  have hgap : 0 < E - e := sub_pos.mpr (lt_of_not_ge hnot)
  let C : ℝ := max (-e) 0 + K₀ + 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hmin : 0 < min 1 ((E - e) / C) := by
    exact lt_min zero_lt_one (div_pos hgap hC)
  obtain ⟨ε, hε, hεsmall⟩ := exists_between hmin
  have hε1 : ε < 1 := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεgap : ε * C < E - e := by
    apply (lt_div_iff₀ hC).mp
    exact lt_of_lt_of_le hεsmall (min_le_right _ _)
  obtain ⟨θ, c, hθ_lower, hθ_upper, hc, hE⟩ := htrial ε hε hε1
  have hquant := quantitative_error (e := e) (c := c)
    (le_of_lt hε) hθ_lower hθ_upper hK₀
  have hfinal : E ≤ e + ε * C := by
    dsimp [C]
    nlinarith
  linarith

end Jellium.Upper
