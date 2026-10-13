import Jellium.Contraction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The discrepancy estimate for the actual contracted smoothed ball.
The only smoothing input is the general BV convolution estimate and the
standard perimeter formula for a ball, independent of this construction. -/

open Set MeasureTheory
open scoped Convolution

namespace Jellium.Contraction

/-- Standard BV facts. The convolution estimate applies to every integrable
BV function, and the ball estimate is its ordinary perimeter formula. -/
structure BVEstimates (perimeterCoefficient : ℝ) where
  bv : (Space → ℝ) → Prop
  variation : (Space → ℝ) → ℝ
  ball_bv : ∀ ρ R : ℝ, bv (sharpBall ρ R)
  variation_nonneg : ∀ f, 0 ≤ variation f
  ball_variation : ∀ ρ R : ℝ, 0 ≤ ρ → 0 ≤ R →
    variation (sharpBall ρ R) ≤ perimeterCoefficient * ρ * R ^ 2
  convolution_error : ∀ (f χ : Space → ℝ),
    bv f → Integrable f → Integrable χ → (∀ x, 0 ≤ χ x) → (∫ x, χ x) = 1 →
    Integrable (fun x => χ x * ‖x‖) →
    (∫ x, |(χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x|) ≤
      variation f * ∫ x, χ x * ‖x‖

theorem kernel_first_moment_le {w : ℝ} (_hw : 0 ≤ w)
    (χ : Space → ℝ) (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ)
    (hχmoment : Integrable (fun x => χ x * ‖x‖))
    (hmass : (∫ x, χ x) = 1)
    (hsupport : Function.support χ ⊆ Metric.closedBall 0 w) :
    (∫ x, χ x * ‖x‖) ≤ w := by
  have hpoint (x : Space) : χ x * ‖x‖ ≤ χ x * w := by
    by_cases hx : χ x = 0
    · simp [hx]
    · have hnorm : ‖x‖ ≤ w := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hsupport hx
      exact mul_le_mul_of_nonneg_left hnorm (hχ x)
  have h := integral_mono hχmoment (hiχ.mul_const w) hpoint
  simpa only [integral_mul_const, hmass, one_mul] using h

theorem smoothBall_l1_error {P ρ R w : ℝ} (laws : BVEstimates P)
    (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (hw : 0 ≤ w)
    (χ : Space → ℝ) (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ)
    (hχmoment : Integrable (fun x => χ x * ‖x‖))
    (hmass : (∫ x, χ x) = 1)
    (hsupport : Function.support χ ⊆ Metric.closedBall 0 w) :
    (∫ x, |smoothBall ρ R χ x - sharpBall ρ R x|) ≤ P * ρ * R ^ 2 * w := by
  calc
    _ ≤ laws.variation (sharpBall ρ R) * ∫ x, χ x * ‖x‖ :=
      laws.convolution_error _ χ (laws.ball_bv ρ R) (sharpBall_integrable ρ R) hiχ hχ hmass hχmoment
    _ ≤ laws.variation (sharpBall ρ R) * w :=
      mul_le_mul_of_nonneg_left
        (kernel_first_moment_le hw χ hχ hiχ hχmoment hmass hsupport) (laws.variation_nonneg _)
    _ ≤ P * ρ * R ^ 2 * w := mul_le_mul_of_nonneg_right (laws.ball_variation ρ R hρ hR) hw

theorem contract_integrable {a : ℝ} (ha : 0 < a) {f : Space → ℝ} (hf : Integrable f) :
    Integrable (contract a f) :=
  (hf.comp_smul (ne_of_gt (inv_pos.mpr ha))).const_mul (a⁻¹ ^ 3)

theorem contracted_smoothBall_l1_error {P ρ R w a : ℝ} (laws : BVEstimates P)
    (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (hw : 0 ≤ w) (ha : 0 < a) (ha1 : a ≤ 1)
    (χ : Space → ℝ) (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ)
    (hχmoment : Integrable (fun x => χ x * ‖x‖))
    (hmass : (∫ x, χ x) = 1)
    (hsupport : Function.support χ ⊆ Metric.closedBall 0 w) :
    (∫ x, |contract a (smoothBall ρ R χ) x - sharpBall ρ R x|) ≤
      P * ρ * R ^ 2 * w +
        6 * ρ * (volume (Metric.ball (0 : Space) R)).toReal * (1 - a) := by
  have hb0 : Integrable (smoothBall ρ R χ) :=
    hiχ.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (sharpBall_integrable ρ R)
  have hb := contract_integrable ha hb0
  have hβ' := contract_integrable ha (sharpBall_integrable ρ R)
  have hβ := sharpBall_integrable ρ R
  have hpoint (x : Space) :
      |contract a (smoothBall ρ R χ) x - sharpBall ρ R x| ≤
      |contract a (smoothBall ρ R χ) x - contract a (sharpBall ρ R) x| +
        |contract a (sharpBall ρ R) x - sharpBall ρ R x| := by
    exact abs_sub_le _ _ _
  have hint := integral_mono (hb.sub hβ).abs ((hb.sub hβ').abs.add (hβ'.sub hβ).abs) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hint
  rw [integral_add (f := fun x => |contract a (smoothBall ρ R χ) x - contract a (sharpBall ρ R) x|)
    (g := fun x => |contract a (sharpBall ρ R) x - sharpBall ρ R x|)
    (hb.sub hβ').abs (hβ'.sub hβ).abs, contract_l1_distance ha] at hint
  exact hint.trans (add_le_add (smoothBall_l1_error laws hρ hR hw χ hχ hiχ hχmoment hmass hsupport)
    (sharp_contraction_l1_le ha ha1 hρ hR))



theorem contracted_smoothed_surface_error {P ρ R A δ a : ℝ} (laws : BVEstimates P)
    (hP : 0 ≤ P) (hρ : 0 ≤ ρ) (hR : 0 < R) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (ha : (1 : ℝ) / 2 ≤ a) (ha1 : a ≤ 1) (haeq : a = 1 - 2 * A * δ / R)
    (χ : Space → ℝ) (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ)
    (hχmoment : Integrable (fun x => χ x * ‖x‖))
    (hmass : (∫ x, χ x) = 1)
    (hsupport : Function.support χ ⊆ Metric.closedBall 0 (A * δ / a)) :
    (∫ x, |contract a (smoothBall ρ R χ) x - sharpBall ρ R x|) ≤
      (2 * P + 12 * (volume (Metric.ball (0 : Space) 1)).toReal) * ρ * A * R ^ 2 * δ := by
  have ha0 : 0 < a := by linarith
  have hw : 0 ≤ A * δ / a := by positivity
  have hbound := contracted_smoothBall_l1_error laws hρ hR.le hw ha0 ha1
    χ hχ hiχ hχmoment hmass hsupport
  have hwle : A * δ / a ≤ 2 * A * δ := by
    apply (div_le_iff₀ ha0).2
    have h := mul_le_mul_of_nonneg_right ha (mul_nonneg hA hδ)
    nlinarith
  have hterm := mul_le_mul_of_nonneg_left hwle (show 0 ≤ P * ρ * R ^ 2 by positivity)
  have hvol : (volume (Metric.ball (0 : Space) R)).toReal =
      R ^ 3 * (volume (Metric.ball (0 : Space) 1)).toReal := by
    simpa only [mul_one] using volume_ball_scale hR.le 1
  have hsecond : 6 * ρ * (volume (Metric.ball (0 : Space) R)).toReal * (1 - a) =
      12 * ρ * (volume (Metric.ball (0 : Space) 1)).toReal * A * R ^ 2 * δ := by
    rw [hvol, haeq]
    field_simp
    ring
  rw [hsecond] at hbound
  nlinarith

theorem contracted_difference_bound {ρ R a : ℝ}
    (hρ : 0 ≤ ρ) (ha : (1 : ℝ) / 2 ≤ a)
    (χ : Space → ℝ) (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ)
    (hmass : (∫ x, χ x) = 1) (x : Space) :
    |contract a (smoothBall ρ R χ) x - sharpBall ρ R x| ≤ 8 * ρ := by
  obtain ⟨hb, hbupper⟩ := contract_bounds ha hρ (smoothBall ρ R χ)
    (fun y => ⟨smoothBall_nonneg χ hρ hχ y, smoothBall_le χ hρ hχ hiχ hmass y⟩) x
  have hβ := sharpBall_nonneg (R := R) hρ x
  have hβupper := sharpBall_le (R := R) hρ x
  exact abs_le.2 ⟨by linarith, by linarith⟩

end Jellium.Contraction
