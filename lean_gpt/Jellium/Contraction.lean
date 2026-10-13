import Jellium.Lower
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
Actual smoothed and contracted ball densities. Convolution and change of
variables are mathlib operations, and the support margin is proved pointwise.
-/

open Set Metric MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace Jellium.Contraction

abbrev Space := EuclideanSpace ℝ (Fin 3)

noncomputable def sharpBall (ρ R : ℝ) : Space → ℝ :=
  (ball 0 R).indicator (fun _ => ρ)

noncomputable def smoothBall (ρ R : ℝ) (χ : Space → ℝ) : Space → ℝ :=
  χ ⋆[lsmul ℝ ℝ] sharpBall ρ R

noncomputable def contract (a : ℝ) (f : Space → ℝ) (x : Space) : ℝ :=
  a⁻¹ ^ 3 * f (a⁻¹ • x)

theorem sharpBall_nonneg {ρ R : ℝ} (hρ : 0 ≤ ρ) (x : Space) :
    0 ≤ sharpBall ρ R x := by
  classical
  by_cases hx : x ∈ ball (0 : Space) R <;> simp [sharpBall, hx, hρ]

theorem sharpBall_le {ρ R : ℝ} (hρ : 0 ≤ ρ) (x : Space) :
    sharpBall ρ R x ≤ ρ := by
  classical
  by_cases hx : x ∈ ball (0 : Space) R <;> simp [sharpBall, hx, hρ]

theorem sharpBall_support (ρ R : ℝ) :
    Function.support (sharpBall ρ R) ⊆ ball 0 R := by
  intro x hx
  by_contra hnot
  exact hx (by simp [sharpBall, hnot])

theorem sharpBall_integrable (ρ R : ℝ) : Integrable (sharpBall ρ R) := by
  exact (integrableOn_const (C := ρ) (s := ball (0 : Space) R) (μ := volume) (measure_ball_lt_top (μ := volume)).ne).integrable_indicator measurableSet_ball

theorem sharpBall_mass (ρ R : ℝ) :
    ∫ x, sharpBall ρ R x = ρ * (volume (ball (0 : Space) R)).toReal := by
  rw [sharpBall, integral_indicator measurableSet_ball, setIntegral_const]
  simp only [smul_eq_mul, measureReal_def]
  ring

theorem smoothBall_nonneg {ρ R : ℝ} (χ : Space → ℝ)
    (hρ : 0 ≤ ρ) (hχ : ∀ x, 0 ≤ χ x) (x : Space) :
    0 ≤ smoothBall ρ R χ x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (hχ y) (sharpBall_nonneg hρ _)

theorem smoothBall_le {ρ R : ℝ} (χ : Space → ℝ)
    (hρ : 0 ≤ ρ) (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ)
    (hmass : ∫ x, χ x = 1) (x : Space) : smoothBall ρ R χ x ≤ ρ := by
  have hbound := convolution_mono_right_of_nonneg
    (f := χ) (g := sharpBall ρ R) (g' := fun _ => ρ)
    (x := x) (hiχ.mul_const ρ) hχ (sharpBall_le hρ) (fun _ => hρ)
  simpa only [smoothBall, convolution_def, lsmul_apply, smul_eq_mul,
    integral_mul_const, hmass, one_mul] using hbound

theorem smoothBall_mass (ρ R : ℝ) (χ : Space → ℝ)
    (hiχ : Integrable χ) (hmass : ∫ x, χ x = 1) :
    ∫ x, smoothBall ρ R χ x = ρ * (volume (ball (0 : Space) R)).toReal := by
  rw [smoothBall, integral_convolution (lsmul ℝ ℝ) hiχ (sharpBall_integrable ρ R), hmass]
  simpa using sharpBall_mass ρ R

theorem smoothBall_support {ρ R w : ℝ} (χ : Space → ℝ)
    (hsupp : Function.support χ ⊆ closedBall 0 w) :
    Function.support (smoothBall ρ R χ) ⊆ ball 0 (R + w) := by
  intro x hx
  obtain ⟨u, hu, v, hv, huv⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
  have hu' : ‖u‖ ≤ w := by simpa only [mem_closedBall, dist_zero_right] using hsupp hu
  have hv' : ‖v‖ < R := by
    simpa only [mem_ball, dist_zero_right] using sharpBall_support ρ R hv
  rw [← huv]
  simp only [mem_ball, dist_zero_right]
  exact (norm_add_le u v).trans_lt (by linarith)

theorem contract_mass {a : ℝ} (ha : 0 < a) (f : Space → ℝ) :
    ∫ x, contract a f x = ∫ x, f x := by
  simp only [contract]
  rw [integral_const_mul, Measure.integral_comp_smul volume f a⁻¹]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    abs_of_pos (by positivity : 0 < (a⁻¹ ^ 3)⁻¹)]
  field_simp

theorem contract_support {a R : ℝ} (ha : 0 < a) (f : Space → ℝ)
    (hsupp : Function.support f ⊆ ball 0 R) :
    Function.support (contract a f) ⊆ ball 0 (a * R) := by
  intro x hx
  have hfx : f (a⁻¹ • x) ≠ 0 := by
    intro hzero
    exact hx (by simp [contract, hzero])
  have hnorm : a⁻¹ * ‖x‖ < R := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)] using hsupp hfx
  have hmul := mul_lt_mul_of_pos_left hnorm ha
  have hcancel : a * a⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ha)
  simpa only [mem_ball, dist_zero_right, ← mul_assoc, hcancel, one_mul] using hmul

theorem contracted_smoothBall_support {ρ R A δ a : ℝ}
    (ha : 0 < a) (hR : R ≠ 0) (haeq : a = 1 - 2 * A * δ / R)
    (χ : Space → ℝ) (hsupp : Function.support χ ⊆ closedBall 0 (A * δ / a)) :
    Function.support (contract a (smoothBall ρ R χ)) ⊆ ball 0 (R - A * δ) := by
  have h := contract_support ha (smoothBall ρ R χ) (smoothBall_support (ρ := ρ) (R := R) χ hsupp)
  have hr : a * (R + A * δ / a) = R - A * δ := by
    have haR : a * R = R - 2 * A * δ := by rw [haeq]; field_simp
    field_simp
    nlinarith
  simpa only [hr] using h

theorem contract_bounds {a ρ : ℝ} (ha : (1 : ℝ) / 2 ≤ a)
    (hρ : 0 ≤ ρ) (f : Space → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ ρ) (x : Space) :
    0 ≤ contract a f x ∧ contract a f x ≤ 8 * ρ := by
  have ha0 : 0 < a := by linarith
  have hi : 0 ≤ a⁻¹ := le_of_lt (inv_pos.mpr ha0)
  have hi2 : a⁻¹ ≤ 2 := by
    have hc : a * a⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ha0)
    nlinarith
  have hipow : a⁻¹ ^ 3 ≤ 8 := by nlinarith [sq_nonneg (a⁻¹ - 1), mul_nonneg hi (sq_nonneg (a⁻¹ - 2))]
  constructor
  · exact mul_nonneg (pow_nonneg hi _) (hf _).1
  · calc
      contract a f x ≤ a⁻¹ ^ 3 * ρ := mul_le_mul_of_nonneg_left (hf _).2 (pow_nonneg hi _)
      _ ≤ 8 * ρ := mul_le_mul_of_nonneg_right hipow hρ



theorem contract_sharpBall {a : ℝ} (ha : 0 < a) (ρ R : ℝ) :
    contract a (sharpBall ρ R) = sharpBall (a⁻¹ ^ 3 * ρ) (a * R) := by
  classical
  funext x
  have hmem : a⁻¹ • x ∈ ball (0 : Space) R ↔ x ∈ ball (0 : Space) (a * R) := by
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    rw [← div_eq_inv_mul, div_lt_iff₀ ha, mul_comm R a]
  by_cases hx : x ∈ ball (0 : Space) (a * R)
  · simp [contract, sharpBall, hx, hmem.mpr hx]
  · have hn : a⁻¹ • x ∉ ball (0 : Space) R := fun h => hx (hmem.mp h)
    simp only [contract, sharpBall, indicator_of_notMem hx, indicator_of_notMem hn, mul_zero]

theorem contract_abs_sub {a : ℝ} (ha : 0 < a) (f g : Space → ℝ) :
    (fun x => |contract a f x - contract a g x|) = contract a (fun x => |f x - g x|) := by
  funext x
  simp only [contract, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < a⁻¹ ^ 3)]

theorem contract_l1_distance {a : ℝ} (ha : 0 < a) (f g : Space → ℝ) :
    (∫ x, |contract a f x - contract a g x|) = ∫ x, |f x - g x| := by
  rw [contract_abs_sub ha, contract_mass ha]

theorem volume_ball_scale {a : ℝ} (ha : 0 ≤ a) (R : ℝ) :
    (volume (ball (0 : Space) (a * R))).toReal =
      a ^ 3 * (volume (ball (0 : Space) R)).toReal := by
  rw [Measure.addHaar_ball_mul volume (0 : Space) ha R, ENNReal.toReal_mul]
  simp [finrank_euclideanSpace, ENNReal.toReal_ofReal (pow_nonneg ha 3)]

theorem sharp_contraction_l1 {a ρ R : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hρ : 0 ≤ ρ) (hR : 0 ≤ R) :
    (∫ x, |contract a (sharpBall ρ R) x - sharpBall ρ R x|) =
      2 * ρ * (volume (ball (0 : Space) R)).toReal * (1 - a ^ 3) := by
  have hi1 : 1 ≤ a⁻¹ := (one_le_inv₀ ha).2 ha1
  have hipow : 1 ≤ a⁻¹ ^ 3 := one_le_pow₀ hi1
  have hlarge : ρ ≤ a⁻¹ ^ 3 * ρ := by nlinarith
  have hsub : ball (0 : Space) (a * R) ⊆ ball (0 : Space) R :=
    ball_subset_ball (by nlinarith)
  have hid : (fun x => |sharpBall (a⁻¹ ^ 3 * ρ) (a * R) x - sharpBall ρ R x|) =
      fun x => sharpBall (a⁻¹ ^ 3 * ρ) (a * R) x + sharpBall ρ R x -
        2 * sharpBall ρ (a * R) x := by
    classical
    funext x
    by_cases hx : x ∈ ball (0 : Space) (a * R)
    · simp only [sharpBall, indicator_of_mem hx, indicator_of_mem (hsub hx)]
      rw [abs_of_nonneg (by linarith)]
      ring
    · by_cases hxR : x ∈ ball (0 : Space) R
      · simp only [sharpBall, indicator_of_notMem hx, indicator_of_mem hxR]
        rw [zero_sub, abs_neg, abs_of_nonneg hρ]
        ring
      · simp [sharpBall, hx, hxR]
  rw [contract_sharpBall ha, hid,
    integral_sub (f := fun x => sharpBall (a⁻¹ ^ 3 * ρ) (a * R) x + sharpBall ρ R x)
      (g := fun x => 2 * sharpBall ρ (a * R) x)
      ((sharpBall_integrable _ _).add (sharpBall_integrable _ _))
      ((sharpBall_integrable _ _).const_mul 2),
    integral_add (sharpBall_integrable _ _) (sharpBall_integrable _ _),
    integral_const_mul, sharpBall_mass, sharpBall_mass, sharpBall_mass,
    volume_ball_scale ha.le]
  field_simp
  ring

theorem sharp_contraction_l1_le {a ρ R : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hρ : 0 ≤ ρ) (hR : 0 ≤ R) :
    (∫ x, |contract a (sharpBall ρ R) x - sharpBall ρ R x|) ≤
      6 * ρ * (volume (ball (0 : Space) R)).toReal * (1 - a) := by
  rw [sharp_contraction_l1 ha ha1 hρ hR]
  have hpoly : 1 - a ^ 3 ≤ 3 * (1 - a) := by
    have hmul := mul_nonneg (show 0 ≤ 1 - a by linarith) (sq_nonneg (a - 1))
    nlinarith [sq_nonneg (a - 1)]
  have h := mul_le_mul_of_nonneg_left hpoly
    (show 0 ≤ 2 * ρ * (volume (ball (0 : Space) R)).toReal by positivity)
  nlinarith

end Jellium.Contraction
