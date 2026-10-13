import Jellium.LowerPhysical
import Jellium.UpperPhysical

/-! The connected Jellium–UEG equality theorem. Both comparisons use the same
state space and charge model. Shell completion and both energy comparisons
are proved from explicit analytic, literature and state-space inputs. -/

open MeasureTheory

namespace Jellium.Conjecture51

universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable [MeasurableAdd₂ V] [MeasurableSub₂ V]
variable {State : Type w} [MeasurableSpace State]
variable {C : TrialState.ChargeModel Spatial.Space V} {h₂ cTF sf ρ eJ eU a B : ℝ}
variable {S : TrialState.StateAPI C State h₂ cTF}

theorem equality (χ : LowerDensity.Mollifier a)
    (lower : LowerPhysical.StandardLaws C S χ ρ eU eJ)
    (upper : UpperPhysical.StandardLaws C S sf ρ eJ)
    {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (localization : UpperDensity.LocalizationLaws C S μ ρ eU)
    (hρ : 0 < ρ) (hh₂ : 0 < h₂) (hcTF : 0 ≤ cTF) (hsf : 0 ≤ sf) (ha : 0 < a)
    (coulomb : Contraction.CoulombInterpolation lower.coulombEnergy B) (hB : 0 ≤ B) :
    eJ = eU := by
  exact le_antisymm
    (LowerPhysical.lower_comparison lower hρ hh₂ ha coulomb hB)
    (UpperPhysical.upper_comparison upper μ localization χ hρ hh₂ hcTF hsf ha)

end Jellium.Conjecture51
