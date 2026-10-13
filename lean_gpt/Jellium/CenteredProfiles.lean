import Jellium.ProfileAverage

/-! Periodic profile lemmas in the fixed-center convention used by the
actual translated base states. These are change-of-origin consequences of
the proved lattice averaging identities. -/

open Set Metric MeasureTheory MeasureTheory.Measure
open Classical

namespace Jellium.CenteredProfiles

open Spatial Jellium.Lattice

private theorem cancel_center (x c h u : Space) : (x - c - h - u) + c = x - h - u := by
  rw [sub_right_comm x c h, sub_right_comm (x - h) c u, sub_add_cancel]

theorem recentered_support {f : Space → ℝ} {c : Space} {r : ℝ}
    (hf : Function.support f ⊆ closedBall c r) :
    Function.support (fun y => f (y + c)) ⊆ closedBall 0 r := by
  intro y hy
  have h := hf hy
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using h

theorem integrable_selected {L : ℝ} (hL : 0 < L) (R a r : ℝ)
    (c x : Space) (z : LatticeIndex) (f : Space → ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hf : Integrable f) :
    Integrable (fun u => selectedCorrection (cube R) a (c + latticeShift L z + u) r
      (fun y => f (y - latticeShift L z - u)) x) (shiftMeasure L) :=
  (ProfileAverage.integrable_translated_profile hL hf (x - latticeShift L z)).indicator
    (measurableSet_selectedBall L R a r c z ha hr)

theorem neutral_plateau {ι : Type*} {L R a d ρ₀ : ℝ}
    (hL : 0 < L) (J : Finset ι) (s : Finset LatticeIndex)
    (c : ι → Space) (r : ι → ℝ) (f : ι → Space → ℝ)
    (hr : ∀ i ∈ J, r i ≤ d) (hf : ∀ i ∈ J, Integrable (f i))
    (hsupport : ∀ i ∈ J, Function.support (f i) ⊆ closedBall (c i) (r i))
    (hcharge : ∀ i ∈ J, (∫ y, f i y) = 0)
    (hcover : ∀ i ∈ J, ∀ z u, u ∈ fundamentalCube L →
      selectedBall (cube R) a (c i + latticeShift L z + u) (r i) → z ∈ s)
    (x : Space) (hx : x ∈ cube (R - 2 * (a + 2 * d))) :
    (∫ u, ρ₀ + ∑ i ∈ J, ∑ z ∈ s,
      selectedCorrection (cube R) a (c i + latticeShift L z + u) (r i)
        (fun y => f i (y - latticeShift L z - u)) x ∂shiftMeasure L) = ρ₀ := by
  have h := ProfileAverage.neutral_plateau_of_selected_cover (ρ₀ := ρ₀) hL J s c r
    (fun i y => f i (y + c i)) hr (fun i hi => (hf i hi).comp_add_right (c i))
    (fun i hi => recentered_support (hsupport i hi))
    (fun i hi => by rw [integral_add_right_eq_self, hcharge i hi]) hcover x hx
  simpa only [cancel_center] using h

theorem selected_average_le {L R a r : ℝ} (hL : 0 < L)
    (s : Finset LatticeIndex) (x c : Space) (f : Space → ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hf : Integrable f) (hnonneg : ∀ y, 0 ≤ f y)
    (hsupport : Function.support f ⊆ closedBall c r) :
    (∫ u, ∑ z ∈ s, selectedCorrection (cube R) a (c + latticeShift L z + u) r
      (fun y => f (y - latticeShift L z - u)) x ∂shiftMeasure L) ≤
        (L ^ 3)⁻¹ * ∫ y, f y := by
  have h := ProfileAverage.selected_profile_average_le (R := R) hL s x c (fun y => f (y + c)) ha hr
    (hf.comp_add_right c) (fun y => hnonneg _) (recentered_support hsupport)
  simpa only [cancel_center, integral_add_right_eq_self] using h

theorem selected_vanishes_outside {L R a r : ℝ} (ha : 0 ≤ a)
    (c x u : Space) (z : LatticeIndex) (f : Space → ℝ)
    (hsupport : Function.support f ⊆ closedBall c r) (hx : x ∉ cube R) :
    selectedCorrection (cube R) a (c + latticeShift L z + u) r
      (fun y => f (y - latticeShift L z - u)) x = 0 := by
  have h := ProfileAverage.selected_profile_vanishes_outside (L := L) ha c x u z
    (fun y => f (y + c)) (recentered_support hsupport) hx
  simpa only [cancel_center] using h

end Jellium.CenteredProfiles
