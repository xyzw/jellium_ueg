import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity

/-!
The scalar reductions surrounding the manuscript's main theorem.

The energy families below are arbitrary real functions. Their physical
scaling relations are explicit hypotheses. This file checks the passage from
equality at kinetic parameter one to equality at every positive parameter,
and the equivalent formulation in terms of the unit-density coupling.
It does not construct the operator model or its scaling laws.
-/

namespace Jellium.EnergyScaling

/-- The density/coupling relation gives exactly the powers six and minus
eight in the parameter reduction. Only the density/coupling law is assumed. -/
theorem parameter_scaling_of_density_scaling
    (energy : ℝ → ℝ → ℝ) (couplingEnergy : ℝ → ℝ)
    (density_scale : ∀ h ρ, 0 < h → 0 < ρ →
      energy h ρ = ρ ^ ((4 : ℝ) / 3) *
        couplingEnergy (h ^ 2 * ρ ^ ((1 : ℝ) / 3)))
    {h ρ : ℝ} (hh : 0 < h) (hρ : 0 < ρ) :
    energy h ρ = (h ^ 8)⁻¹ * energy 1 (h ^ 6 * ρ) := by
  have hpow4 : (h ^ 6 * ρ) ^ ((4 : ℝ) / 3) = h ^ 8 * ρ ^ ((4 : ℝ) / 3) := by
    rw [Real.mul_rpow (pow_nonneg hh.le 6) hρ.le,
      ← Real.rpow_natCast_mul hh.le]
    norm_num
  have hpow1 : (h ^ 6 * ρ) ^ ((1 : ℝ) / 3) = h ^ 2 * ρ ^ ((1 : ℝ) / 3) := by
    rw [Real.mul_rpow (pow_nonneg hh.le 6) hρ.le,
      ← Real.rpow_natCast_mul hh.le]
    norm_num
  rw [density_scale h ρ hh hρ,
    density_scale 1 (h ^ 6 * ρ) zero_lt_one (mul_pos (pow_pos hh 6) hρ), hpow4, hpow1]
  simp only [one_pow, one_mul]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 8 hh.ne'), one_mul]

/-- The reduction at the start of the proof section. Positivity of the
rescaled density discharges the hypothesis of the unit-parameter comparison. -/
theorem equality_of_unit_parameter
    (jellium ueg : ℝ → ℝ → ℝ)
    (jellium_scale : ∀ h ρ, 0 < h → 0 < ρ →
      jellium h ρ = (h ^ 8)⁻¹ * jellium 1 (h ^ 6 * ρ))
    (ueg_scale : ∀ h ρ, 0 < h → 0 < ρ →
      ueg h ρ = (h ^ 8)⁻¹ * ueg 1 (h ^ 6 * ρ))
    (unit_equality : ∀ ρ, 0 < ρ → jellium 1 ρ = ueg 1 ρ)
    {h ρ : ℝ} (hh : 0 < h) (hρ : 0 < ρ) :
    jellium h ρ = ueg h ρ := by
  rw [jellium_scale h ρ hh hρ, ueg_scale h ρ hh hρ,
    unit_equality (h ^ 6 * ρ) (mul_pos (pow_pos hh 6) hρ)]

/-- Equality at all positive physical parameters is equivalent to equality
of the unit-density coupling functions. Specialization at `h = sqrt λ`
and density one covers every positive coupling. -/
theorem equality_iff_coupling_equality
    (jellium ueg : ℝ → ℝ → ℝ) (jelliumCoupling uegCoupling : ℝ → ℝ)
    (jellium_scale : ∀ h ρ, 0 < h → 0 < ρ →
      jellium h ρ = ρ ^ ((4 : ℝ) / 3) *
        jelliumCoupling (h ^ 2 * ρ ^ ((1 : ℝ) / 3)))
    (ueg_scale : ∀ h ρ, 0 < h → 0 < ρ →
      ueg h ρ = ρ ^ ((4 : ℝ) / 3) *
        uegCoupling (h ^ 2 * ρ ^ ((1 : ℝ) / 3))) :
    (∀ h ρ, 0 < h → 0 < ρ → jellium h ρ = ueg h ρ) ↔
      (∀ coupling, 0 < coupling → jelliumCoupling coupling = uegCoupling coupling) := by
  constructor
  · intro equality coupling hcoupling
    have hsqrt : 0 < Real.sqrt coupling := Real.sqrt_pos.2 hcoupling
    have h := equality (Real.sqrt coupling) 1 hsqrt zero_lt_one
    rw [jellium_scale _ _ hsqrt zero_lt_one, ueg_scale _ _ hsqrt zero_lt_one] at h
    simpa only [Real.one_rpow, mul_one, one_mul, Real.sq_sqrt hcoupling.le] using h
  · intro equality h ρ hh hρ
    have hcoupling : 0 < h ^ 2 * ρ ^ ((1 : ℝ) / 3) :=
      mul_pos (pow_pos hh 2) (Real.rpow_pos_of_pos hρ _)
    rw [jellium_scale h ρ hh hρ, ueg_scale h ρ hh hρ,
      equality _ hcoupling]

end Jellium.EnergyScaling
