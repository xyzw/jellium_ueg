import Jellium.UpperBackground
import Jellium.UpperMixture
import Jellium.MeasurableTrial
import Jellium.PackingParameters
import Jellium.Domains

/-! Named standard inputs for the physical upper comparison. None is a
packing construction, a global trial bound, or a bounded-layer conclusion. -/

open MeasureTheory

namespace Jellium.UpperPhysical

abbrev Space := Spatial.Space
noncomputable def ballFactor : ℝ := Real.pi * 4 / 3

theorem ballFactor_pos : 0 < ballFactor := by
  dsimp [ballFactor]
  positivity

universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable {State : Type w} [MeasurableSpace State]
variable (C : TrialState.ChargeModel Space V) {h₂ cTF : ℝ}
variable (S : TrialState.StateAPI C State h₂ cTF)

/-- Standard physical laws on one and the same charge and Fock-state model.
The local ball law is the canonical ball limit followed by rotation averaging.
The separate localization input will characterize the same UEG energy. -/
structure StandardLaws (sf ρ eJ : ℝ) where
  measure_eq : C.measure = volume
  dirichlet : UpperConstruction.SobolevDirichlet C S sf
  coulomb : UpperConstruction.CoulombLaws C sf
  translations : MeasurableTrial.ChargeTranslations C
  stateTranslations : MeasurableTrial.StateTranslations C S translations
  fock : MeasurableTrial.FockOperations C S
  observables : UpperMixture.ObservableLaws C S
  mixtures : Variational.MixtureLaws C S
  representations : UpperConstruction.Representations C
  bounded_potential : UpperBackground.BoundedPotentialLaw C
  convolution : SmoothCube.ConvolutionSobolevLaws dirichlet.H1 dirichlet.energy
  vitali : Packing.VitaliApproximation ballFactor
  balls : ∀ ε : ℝ, 0 < ε → ∃ rstar : ℝ, 0 < rstar ∧
    UpperConstruction.NearGroundBallLaw S ballFactor ρ eJ ε rstar

variable {C S} {sf ρ eJ : ℝ}

theorem StandardLaws.ball_volume (laws : StandardLaws C S sf ρ eJ)
    (z : Space) (r : ℝ) (hr : 0 ≤ r) :
    C.measure.real (Metric.closedBall z r) = ballFactor * r ^ 3 := by
  rw [laws.measure_eq, Domains.closedBall_volume_real z r hr]
  rfl

theorem StandardLaws.translation_preserving (laws : StandardLaws C S sf ρ eJ)
    (u : Space) : MeasurePreserving (fun x : Space => x - u) C.measure C.measure := by
  rw [laws.measure_eq]
  exact measurePreserving_sub_right volume u

end Jellium.UpperPhysical
