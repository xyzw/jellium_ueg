import Jellium.Packing
import Jellium.Spatial

/-! Parameter selection in the final upper comparison. A single fixed collar
width and surface constant work for every packing and every box size. -/

open MeasureTheory

namespace Jellium.Packing

theorem exists_packing_for_error
    {ρ κ a C ε rstar : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (ha : 0 ≤ a) (_hC : 0 ≤ C)
    (hε : 0 < ε) (hε1 : ε < 1) (vitali : VitaliApproximation κ) :
    ∃ rmin : ℝ, 0 < rmin ∧ 2 * a ≤ rmin ∧ rstar ≤ rmin ∧
      C / (κ * rmin) ≤ ε ∧ Nonempty (NeutralPacking ρ κ a rmin ε) := by
  let rmin := max 1 (max (2 * a) (max rstar (C / (κ * ε))))
  have hr1 : 1 ≤ rmin := le_max_left _ _
  have hrmin : 0 < rmin := lt_of_lt_of_le zero_lt_one hr1
  have hrest : max (2 * a) (max rstar (C / (κ * ε))) ≤ rmin := le_max_right _ _
  have hroom : 2 * a ≤ rmin := le_trans (le_max_left _ _) hrest
  have hstar : rstar ≤ rmin := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hrest)
  have hquot : C / (κ * ε) ≤ rmin := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hrest)
  have hsmall : C / (κ * rmin) ≤ ε := by
    apply (div_le_iff₀ (mul_pos hκ hrmin)).2
    have h := (div_le_iff₀ (mul_pos hκ hε)).1 hquot
    nlinarith
  exact ⟨rmin, hrmin, hroom, hstar, hsmall,
    exists_neutral_packing hρ hκ hε hε1 ha hrmin vitali⟩

theorem physical_coverage_bounds
    {ρ κ ε a rmin : ℝ} (p : NeutralPacking ρ κ a rmin ε)
    (ha : 0 ≤ a)
    (hballs : ∀ i, volume.real (Metric.closedBall (p.center i) (p.radius i)) = κ * p.radius i ^ 3) :
    1 - ε ≤ (∑ i, κ * p.radius i ^ 3) / p.length ^ 3 ∧
      (∑ i, κ * p.radius i ^ 3) / p.length ^ 3 ≤ 1 := by
  refine ⟨p.coverage, ?_⟩
  exact coverage_le_one p ha volume (Spatial.volume_cube_ne_top p.length) hballs
    (Spatial.volume_cube_toReal p.length_pos.le)

end Jellium.Packing
