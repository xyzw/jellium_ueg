import Jellium.Conjecture51
import Jellium.EnergyScaling

/-!
The current manuscript's main theorem, including its parameter reduction.

For each intended fixed finite spin multiplicity, an abstract state and charge
model is supplied, with the unit-parameter construction at every positive
density. The physical spin space remains part of that model's interpretation.
The density/coupling scaling laws are
explicit inputs from the setting section. Both formulations below depend on
the proved lower and upper comparisons through `Conjecture51.equality`.

The general facts in the manuscript's Basic facts section remain inputs to
the state, Coulomb and localization interfaces.
-/

open MeasureTheory

namespace Jellium.Main

universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable [MeasurableAdd₂ V] [MeasurableSub₂ V]
variable {State : Type w} [MeasurableSpace State]
variable {C : TrialState.ChargeModel Spatial.Space V} {cTF sf a : ℝ}
variable {S : TrialState.StateAPI C State 1 cTF}
variable {U : Type*} [MeasurableSpace U] {μ : Measure U} [IsProbabilityMeasure μ]

/-- The existing fixed-density inputs, collected without assuming either
comparison or equality. The interpolation constant may depend on the model. -/
structure UnitParameterInputs (χ : LowerDensity.Mollifier a)
    (C : TrialState.ChargeModel Spatial.Space V)
    (S : TrialState.StateAPI C State 1 cTF)
    (μ : Measure U) [IsProbabilityMeasure μ] (sf ρ eJ eU : ℝ) where
  lower : LowerPhysical.StandardLaws C S χ ρ eU eJ
  upper : UpperPhysical.StandardLaws C S sf ρ eJ
  localization : UpperDensity.LocalizationLaws C S μ ρ eU
  interpolationConstant : ℝ
  interpolation_nonnegative : 0 ≤ interpolationConstant
  interpolation : Contraction.CoulombInterpolation lower.coulombEnergy interpolationConstant

variable {χ : LowerDensity.Mollifier a}

/-- The unit-parameter result uses the full connected construction. -/
theorem unit_parameter_equality {ρ eJ eU : ℝ}
    (inputs : UnitParameterInputs χ C S μ sf ρ eJ eU)
    (hρ : 0 < ρ) (hcTF : 0 ≤ cTF) (hsf : 0 ≤ sf) (ha : 0 < a) :
    eJ = eU :=
  Conjecture51.equality χ inputs.lower inputs.upper μ inputs.localization
    hρ zero_lt_one hcTF hsf ha inputs.interpolation inputs.interpolation_nonnegative

/-- Theorem `thm:attack_equality` at every positive hbar and
density. The powers six and minus eight are derived from density scaling. -/
theorem equality
    (jellium ueg : ℝ → ℝ → ℝ) (jelliumCoupling uegCoupling : ℝ → ℝ)
    (jellium_scale : ∀ h ρ, 0 < h → 0 < ρ →
      jellium h ρ = ρ ^ ((4 : ℝ) / 3) *
        jelliumCoupling (h ^ 2 * ρ ^ ((1 : ℝ) / 3)))
    (ueg_scale : ∀ h ρ, 0 < h → 0 < ρ →
      ueg h ρ = ρ ^ ((4 : ℝ) / 3) *
        uegCoupling (h ^ 2 * ρ ^ ((1 : ℝ) / 3)))
    (inputs : ∀ ρ, 0 < ρ → UnitParameterInputs χ C S μ sf ρ (jellium 1 ρ) (ueg 1 ρ))
    (hcTF : 0 ≤ cTF) (hsf : 0 ≤ sf) (ha : 0 < a)
    {h ρ : ℝ} (hh : 0 < h) (hρ : 0 < ρ) :
    jellium h ρ = ueg h ρ := by
  apply EnergyScaling.equality_of_unit_parameter jellium ueg
    (fun _ _ hh hρ => EnergyScaling.parameter_scaling_of_density_scaling
      jellium jelliumCoupling jellium_scale hh hρ)
    (fun _ _ hh hρ => EnergyScaling.parameter_scaling_of_density_scaling
      ueg uegCoupling ueg_scale hh hρ) _ hh hρ
  intro ρ hρ
  exact unit_parameter_equality (inputs ρ hρ) hρ hcTF hsf ha

/-- The equivalent positive-coupling formulation of the main theorem. -/
theorem coupling_equality
    (jellium ueg : ℝ → ℝ → ℝ) (jelliumCoupling uegCoupling : ℝ → ℝ)
    (jellium_scale : ∀ h ρ, 0 < h → 0 < ρ →
      jellium h ρ = ρ ^ ((4 : ℝ) / 3) *
        jelliumCoupling (h ^ 2 * ρ ^ ((1 : ℝ) / 3)))
    (ueg_scale : ∀ h ρ, 0 < h → 0 < ρ →
      ueg h ρ = ρ ^ ((4 : ℝ) / 3) *
        uegCoupling (h ^ 2 * ρ ^ ((1 : ℝ) / 3)))
    (inputs : ∀ ρ, 0 < ρ → UnitParameterInputs χ C S μ sf ρ (jellium 1 ρ) (ueg 1 ρ))
    (hcTF : 0 ≤ cTF) (hsf : 0 ≤ sf) (ha : 0 < a)
    {coupling : ℝ} (hcoupling : 0 < coupling) :
    jelliumCoupling coupling = uegCoupling coupling := by
  apply (EnergyScaling.equality_iff_coupling_equality
    jellium ueg jelliumCoupling uegCoupling jellium_scale ueg_scale).mp _ coupling hcoupling
  intro h ρ hh hρ
  exact equality jellium ueg jelliumCoupling uegCoupling jellium_scale ueg_scale
    inputs hcTF hsf ha hh hρ

end Jellium.Main
