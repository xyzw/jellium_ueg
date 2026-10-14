import Jellium.OrbitalSampling
import Jellium.DomainLayers
import Mathlib.Probability.ConditionalProbability

/-! The concrete uniform law for centers in a trimmed spherical annulus. -/

open Set Metric MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace Jellium.OrbitalAnnulus

open Domains

def centerRegion (R S : ℝ) : Set Space :=
  ball 0 (S - 1) \ closedBall 0 (R + 1)

noncomputable def centerVolume (R S : ℝ) : ℝ :=
  RadialShells.layerMass (R + 1) (S - 1)

noncomputable def centerLaw (R S : ℝ) : Measure Space :=
  ProbabilityTheory.cond volume (centerRegion R S)

theorem centerVolume_eq (R S : ℝ) :
    centerVolume R S = ballVolume (S - 1) - ballVolume (R + 1) := by
  unfold centerVolume RadialShells.layerMass ballVolume
  ring

theorem measurableSet_centerRegion (R S : ℝ) : MeasurableSet (centerRegion R S) :=
  measurableSet_ball.diff measurableSet_closedBall

theorem centerRegion_volume_ne_top (R S : ℝ) : volume (centerRegion R S) ≠ ⊤ :=
  measure_ne_top_of_subset sdiff_subset (ball_volume_ne_top 0 (S - 1))

theorem centerRegion_volume (R S : ℝ) (hR : 0 < R) (hS : R + 3 ≤ S) :
    volume.real (centerRegion R S) = centerVolume R S := by
  unfold centerRegion
  rw [measureReal_sdiff (closedBall_subset_ball (by linarith)) measurableSet_closedBall
    (ball_volume_ne_top 0 (S - 1)), ball_volume_real _ _ (by linarith),
    closedBall_volume_real _ _ (by linarith)]
  unfold ballVolume centerVolume RadialShells.layerMass
  ring

theorem centerVolume_pos {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) :
    0 < centerVolume R S :=
  RadialShells.layerMass_pos _ _ (by linarith) (by linarith)

theorem centerRegion_volume_ne_zero {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) :
    volume (centerRegion R S) ≠ 0 := by
  have h := centerVolume_pos hR hS
  rw [← centerRegion_volume R S hR hS, measureReal_def] at h
  exact (ENNReal.toReal_pos_iff.mp h).1.ne'

theorem centerLaw_probability {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) :
    IsProbabilityMeasure (centerLaw R S) :=
  cond_isProbabilityMeasure_of_finite (centerRegion_volume_ne_zero hR hS)
    (centerRegion_volume_ne_top R S)

instance centerLaw_atomless (R S : ℝ) : NullSingletonClass (centerLaw R S) := by
  refine ⟨fun x => ?_⟩
  exact (show centerLaw R S ≪ (volume : Measure Space) from
    cond_absolutelyContinuous) (measure_singleton x)

theorem ae_mem_centerRegion (R S : ℝ) :
    ∀ᵐ x ∂centerLaw R S, x ∈ centerRegion R S := by
  exact ae_smul_measure (ae_restrict_mem (measurableSet_centerRegion R S)) _

theorem integral_centerLaw {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S)
    (f : Space → ℝ) :
    (∫ x, f x ∂centerLaw R S) =
      (centerVolume R S)⁻¹ * ∫ x in centerRegion R S, f x := by
  unfold centerLaw ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv]
  change (volume.real (centerRegion R S))⁻¹ * _ = _
  rw [centerRegion_volume R S hR hS]

theorem integrable_centerLaw {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S)
    {f : Space → ℝ} (hf : IntegrableOn f (centerRegion R S)) :
    Integrable f (centerLaw R S) := by
  exact hf.smul_measure (ENNReal.inv_ne_top.mpr (centerRegion_volume_ne_zero hR hS))

theorem ae_centers {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) (n : ℕ) :
    ∀ᵐ x : Fin n → Space ∂OrbitalSampling.sampleMeasure (centerLaw R S) n,
      Function.Injective x ∧ ∀ i, R + 1 < ‖x i‖ ∧ ‖x i‖ < S - 1 := by
  let := centerLaw_probability hR hS
  filter_upwards [OrbitalSampling.ae_injective (centerLaw R S),
    OrbitalSampling.ae_all_coordinates (centerLaw R S) (ae_mem_centerRegion R S)] with x hx hm
  refine ⟨hx, fun i => ?_⟩
  have hi := hm i
  simpa only [centerRegion, mem_sdiff, mem_ball, mem_closedBall, dist_zero_right,
    not_le, and_comm] using hi

end Jellium.OrbitalAnnulus
