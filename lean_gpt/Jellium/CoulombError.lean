import Jellium.Contraction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Positivity

/-! The standard L¹/L∞ Coulomb interpolation inequality yields a vanishing
normalized discrepancy for the actual surface-order L¹ error. -/

open MeasureTheory Filter Topology

namespace Jellium.Contraction

/-- The usual Coulomb L¹/L∞ bound for arbitrary signed integrable bounded
charges in three dimensions. This is a standard analytic input. -/
def CoulombInterpolation (energy : (Space → ℝ) → ℝ) (C : ℝ) : Prop :=
  ∀ (f : Space → ℝ) (L : ℝ), Integrable f → 0 ≤ L →
    (∀ x, |f x| ≤ L) →
    0 ≤ energy f ∧ energy f ≤ C * (∫ x, |f x|) ^ ((5 : ℝ) / 3) * L ^ ((1 : ℝ) / 3)

theorem rpow_cube_five_thirds {t : ℝ} (ht : 0 ≤ t) :
    (t ^ 3) ^ ((5 : ℝ) / 3) = t ^ 5 := by
  rw [← Real.rpow_natCast t 3, ← Real.rpow_mul ht]
  norm_num

theorem coulomb_fifth_power_bound
    {energy : (Space → ℝ) → ℝ} {C B L t : ℝ}
    (law : CoulombInterpolation energy C) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (f : Space → ℝ) (hf : Integrable f)
    (hbound : ∀ x, |f x| ≤ L) (hl1 : (∫ x, |f x|) ≤ B * t ^ 3) :
    0 ≤ energy f ∧ energy f ≤ (C * B ^ ((5 : ℝ) / 3) * L ^ ((1 : ℝ) / 3)) * t ^ 5 := by
  obtain ⟨hnonneg, henergy⟩ := law f L hf hL hbound
  refine ⟨hnonneg, henergy.trans ?_⟩
  have hpow := Real.rpow_le_rpow (integral_nonneg (fun x => abs_nonneg (f x))) hl1
    (by norm_num : (0 : ℝ) ≤ 5 / 3)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
    (Real.rpow_nonneg hL ((1 : ℝ) / 3))
  rw [Real.mul_rpow hB (pow_nonneg ht 3), rpow_cube_five_thirds ht] at hmul
  nlinarith

theorem normalized_coulomb_tendsto_zero
    {energy : (Space → ℝ) → ℝ} {C B L v : ℝ}
    (law : CoulombInterpolation energy C) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hv : 0 < v)
    (size : ℕ → ℝ) (hsize : Tendsto size atTop atTop)
    (f : ℕ → Space → ℝ)
    (hdata : ∀ᶠ n in atTop, 0 < size n ∧ Integrable (f n) ∧
      (∀ x, |f n x| ≤ L) ∧ (∫ x, |f n x|) ≤ B * size n ^ 3) :
    Tendsto (fun n => energy (f n) / (v * size n ^ 6)) atTop (𝓝 0) := by
  let K := C * B ^ ((5 : ℝ) / 3) * L ^ ((1 : ℝ) / 3)
  have hupper : Tendsto (fun n => (K / v) * (size n)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hsize)
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hdata] with n hn
    exact div_nonneg (law (f n) L hn.2.1 hL hn.2.2.1).1 (by positivity)
  · filter_upwards [hdata] with n hn
    have h := (coulomb_fifth_power_bound law hC hB hL hn.1.le (f n) hn.2.1 hn.2.2.1 hn.2.2.2).2
    calc
      energy (f n) / (v * size n ^ 6) ≤ K * size n ^ 5 / (v * size n ^ 6) :=
        div_le_div_of_nonneg_right h (by positivity)
      _ = (K / v) * (size n)⁻¹ := by
        have hs : size n ≠ 0 := ne_of_gt hn.1
        field_simp

end Jellium.Contraction
