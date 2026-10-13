import Jellium.Domains
import Jellium.RadialShells
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Distance layers and the radial double layers of the actual lattice domains. -/

open Set Metric Filter Topology MeasureTheory
open scoped BigOperators

namespace Jellium.Domains

theorem cthickening_iUnion_finite {I : Type*} [Finite I]
    (A : I → Set Space) (h : ℝ) (hh : 0 ≤ h) :
    cthickening h (⋃ i, A i) = ⋃ i, cthickening h (A i) := by
  simp_rw [cthickening_eq_biUnion_closedBall _ hh]
  rw [closure_iUnion_of_finite]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨y, ⟨i, hy⟩, hx⟩
    exact ⟨i, y, hy, hx⟩
  · rintro ⟨i, y, hy, hx⟩
    exact ⟨y, ⟨i, hy⟩, hx⟩

theorem lattice_cthickening (R h : ℝ) (hR : 0 < R) (hh : 0 ≤ h) (m : ℕ) :
    cthickening h (latticeBalls R m) =
      ⋃ i : Grid m, closedBall (center R i) (R + h) := by
  unfold latticeBalls
  rw [cthickening_iUnion_finite _ h hh]
  simp only [cthickening_ball hh hR, add_comm h R]

theorem iUnion_sdiff_iUnion {I : Type*} (A B C : I → Set Space)
    (hAB : ∀ i, A i ⊆ B i) (hBC : ∀ i, B i ⊆ C i)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j))) :
    (⋃ i, B i) \ (⋃ i, A i) = ⋃ i, B i \ A i := by
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, hi, fun h => hnot (mem_iUnion.mpr ⟨i, h⟩)⟩
  · intro hx
    obtain ⟨i, hi, hnot⟩ := mem_iUnion.mp hx
    refine ⟨mem_iUnion.mpr ⟨i, hi⟩, ?_⟩
    intro hA
    obtain ⟨j, hj⟩ := mem_iUnion.mp hA
    by_cases hij : i = j
    · subst j
      exact hnot hj
    · exact Set.disjoint_left.mp (hC hij) (hBC i hi) (hBC j (hAB j hj))

def outerFirstLayer (Ω : Set Space) (h : ℝ) : Set Space := cthickening h Ω \ Ω

def outerSecondLayer (Ω : Set Space) (h : ℝ) : Set Space :=
  cthickening (2 * h) Ω \ cthickening h Ω

theorem lattice_outer_first (R h : ℝ) (hh : 0 ≤ h) (hR : 4 * h < R) (m : ℕ) :
    outerFirstLayer (latticeBalls R m) h =
      ⋃ i : Grid m, closedBall (center R i) (R + h) \ ball (center R i) R := by
  have hRpos : 0 < R := by linarith
  unfold outerFirstLayer
  rw [lattice_cthickening R h hRpos hh]
  unfold latticeBalls
  apply iUnion_sdiff_iUnion _ _ (fun i : Grid m => closedBall (center R i) (R + 2 * h))
  · intro i
    exact (ball_subset_closedBall).trans (closedBall_subset_closedBall (by linarith))
  · intro i
    exact closedBall_subset_closedBall (by linarith)
  · exact enlarged_closed_balls_pairwise_disjoint R h hh hR m

theorem lattice_outer_second (R h : ℝ) (hh : 0 ≤ h) (hR : 4 * h < R) (m : ℕ) :
    outerSecondLayer (latticeBalls R m) h =
      ⋃ i : Grid m, closedBall (center R i) (R + 2 * h) \
        closedBall (center R i) (R + h) := by
  have hRpos : 0 < R := by linarith
  unfold outerSecondLayer
  rw [lattice_cthickening R (2 * h) hRpos (by positivity), lattice_cthickening R h hRpos hh]
  apply iUnion_sdiff_iUnion _ _ (fun i : Grid m => closedBall (center R i) (R + 2 * h))
  · intro i
    exact closedBall_subset_closedBall (by linarith)
  · intro i
    exact Set.Subset.rfl
  · exact enlarged_closed_balls_pairwise_disjoint R h hh hR m

/-- The radial boundary point nearest to an interior point of a ball. -/
theorem exists_radial_boundary (c x : Space) (R : ℝ) (hR : 0 ≤ R)
    (hx : dist x c ≤ R) :
    ∃ y : Space, dist y c = R ∧ dist x y = R - dist x c := by
  by_cases heq : x = c
  · subst x
    obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (E := Space) (x := c)).2 hR
    refine ⟨y, hy, ?_⟩
    simpa only [mem_sphere, dist_self, sub_zero, dist_comm] using hy
  · have hd : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
    let a : ℝ := R / ‖x - c‖
    let y : Space := c + a • (x - c)
    have ha : 0 ≤ a := div_nonneg hR hd.le
    have ha1 : 1 ≤ a := by
      apply (le_div_iff₀ hd).2
      simpa only [one_mul, dist_eq_norm] using hx
    have hy : y - c = a • (x - c) := by dsimp [y]; abel
    have hxy : x - y = (1 - a) • (x - c) := by
      dsimp [y]
      rw [sub_smul, one_smul]
      abel
    refine ⟨y, ?_, ?_⟩
    · rw [dist_eq_norm, hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      exact div_mul_cancel₀ R (ne_of_gt hd)
    · rw [dist_eq_norm, hxy, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : 1 - a ≤ 0), dist_eq_norm]
      dsimp [a]
      field_simp
      ring

/-- A component sphere is outside the entire separated union. -/
theorem component_sphere_complement (R : ℝ) (hR : 0 < R) {m : ℕ}
    (i : Grid m) (y : Space) (hy : dist y (center R i) = R) :
    y ∈ (latticeBalls R m)ᶜ := by
  intro hmem
  obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
  by_cases hij : i = j
  · subst j
    exact (mem_ball.mp hj).ne hy
  · have hsep := center_separation R hR.le i j hij
    have htri := dist_triangle (center R i) y (center R j)
    rw [dist_comm (center R i) y, hy] at htri
    have hj' := mem_ball.mp hj
    linarith

/-- The distance to the complement, evaluated inside one component ball. -/
theorem lattice_inner_distance (R : ℝ) (hR : 0 < R) {m : ℕ}
    (i : Grid m) (x : Space) (hx : x ∈ ball (center R i) R) :
    infDist x (latticeBalls R m)ᶜ = R - dist x (center R i) := by
  obtain ⟨y, hy, hxy⟩ := exists_radial_boundary (center R i) x R hR.le (mem_ball.mp hx).le
  have hyout := component_sphere_complement R hR i y hy
  apply le_antisymm
  · exact hxy ▸ infDist_le_dist_of_mem hyout
  · apply (le_infDist ⟨y, hyout⟩).2
    intro z hz
    have hzball : z ∉ ball (center R i) R := by
      intro hzin
      exact hz (mem_iUnion.mpr ⟨i, hzin⟩)
    have hzR : R ≤ dist z (center R i) := le_of_not_gt hzball
    have htri := dist_triangle z x (center R i)
    rw [dist_comm z x] at htri
    linarith

def innerFirstLayer (Ω : Set Space) (h : ℝ) : Set Space :=
  {x | x ∈ Ω ∧ infDist x Ωᶜ ≤ h}

def innerSecondLayer (Ω : Set Space) (h : ℝ) : Set Space :=
  {x | x ∈ Ω ∧ h < infDist x Ωᶜ ∧ infDist x Ωᶜ ≤ 2 * h}

theorem lattice_inner_first (R h : ℝ) (hR : 0 < R) (m : ℕ) :
    innerFirstLayer (latticeBalls R m) h =
      ⋃ i : Grid m, ball (center R i) R \ ball (center R i) (R - h) := by
  ext x
  constructor
  · rintro ⟨hx, hd⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [lattice_inner_distance R hR i x hi] at hd
    refine mem_iUnion.mpr ⟨i, hi, ?_⟩
    intro hinner
    have := mem_ball.mp hinner
    linarith
  · intro hx
    obtain ⟨i, hi, hnot⟩ := mem_iUnion.mp hx
    refine ⟨mem_iUnion.mpr ⟨i, hi⟩, ?_⟩
    rw [lattice_inner_distance R hR i x hi]
    have hd : R - h ≤ dist x (center R i) := le_of_not_gt hnot
    linarith

theorem lattice_inner_second (R h : ℝ) (hh : 0 ≤ h) (hR : 0 < R) (m : ℕ) :
    innerSecondLayer (latticeBalls R m) h =
      ⋃ i : Grid m, ball (center R i) (R - h) \ ball (center R i) (R - 2 * h) := by
  ext x
  constructor
  · rintro ⟨hx, hd1, hd2⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [lattice_inner_distance R hR i x hi] at hd1 hd2
    refine mem_iUnion.mpr ⟨i, ?_, ?_⟩
    · exact show dist x (center R i) < R - h by linarith
    · exact show ¬ dist x (center R i) < R - 2 * h by linarith
  · intro hx
    obtain ⟨i, hi, hnot⟩ := mem_iUnion.mp hx
    have hiR : x ∈ ball (center R i) R := by
      exact lt_of_lt_of_le (mem_ball.mp hi) (by linarith)
    refine ⟨mem_iUnion.mpr ⟨i, hiR⟩, ?_, ?_⟩ <;>
      rw [lattice_inner_distance R hR i x hiR]
    · have hi' := mem_ball.mp hi
      linarith
    · have hd : R - 2 * h ≤ dist x (center R i) := le_of_not_gt hnot
      linarith

theorem closedBall_volume_ne_top (c : Space) (r : ℝ) :
    volume (closedBall c r) ≠ ⊤ := by
  rw [EuclideanSpace.volume_closedBall_fin_three]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

theorem ball_volume_ne_top (c : Space) (r : ℝ) : volume (ball c r) ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
    (lt_top_iff_ne_top.mpr (closedBall_volume_ne_top c r)))

theorem closed_open_shell_volume (c : Space) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    volume.real (closedBall c b \ ball c a) = RadialShells.layerMass a b := by
  rw [measureReal_sdiff (ball_subset_closedBall.trans (closedBall_subset_closedBall hab))
    measurableSet_ball (closedBall_volume_ne_top c b), closedBall_volume_real c b (ha.trans hab),
    ball_volume_real c a ha]
  unfold ballVolume RadialShells.layerMass
  ring

theorem closed_closed_shell_volume (c : Space) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    volume.real (closedBall c b \ closedBall c a) = RadialShells.layerMass a b := by
  rw [measureReal_sdiff (closedBall_subset_closedBall hab) measurableSet_closedBall
    (closedBall_volume_ne_top c b), closedBall_volume_real c b (ha.trans hab),
    closedBall_volume_real c a ha]
  unfold ballVolume RadialShells.layerMass
  ring

theorem open_open_shell_volume (c : Space) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    volume.real (ball c b \ ball c a) = RadialShells.layerMass a b := by
  rw [measureReal_sdiff (ball_subset_ball hab) measurableSet_ball (ball_volume_ne_top c b),
    ball_volume_real c b (ha.trans hab), ball_volume_real c a ha]
  unfold ballVolume RadialShells.layerMass
  ring

theorem lattice_outer_first_volume (R h : ℝ) (hh : 0 ≤ h) (hR : 4 * h < R) (m : ℕ) :
    volume.real (outerFirstLayer (latticeBalls R m) h) =
      (m : ℝ) ^ 3 * RadialShells.layerMass R (R + h) := by
  have hdis : Pairwise (fun i j : Grid m =>
      Disjoint (closedBall (center R i) (R + h) \ ball (center R i) R)
        (closedBall (center R j) (R + h) \ ball (center R j) R)) := by
    intro i j hij
    apply (enlarged_closed_balls_pairwise_disjoint R h hh hR m hij).mono
    · exact sdiff_subset.trans (closedBall_subset_closedBall (by linarith))
    · exact sdiff_subset.trans (closedBall_subset_closedBall (by linarith))
  rw [lattice_outer_first R h hh hR m,
    measureReal_iUnion_fintype hdis (fun _ => measurableSet_closedBall.diff measurableSet_ball)
      (fun i => measure_ne_top_of_subset sdiff_subset (closedBall_volume_ne_top (center R i) (R + h)))]
  simp_rw [closed_open_shell_volume _ R (R + h) (by linarith) (by linarith)]
  simp

theorem lattice_outer_second_volume (R h : ℝ) (hh : 0 ≤ h) (hR : 4 * h < R) (m : ℕ) :
    volume.real (outerSecondLayer (latticeBalls R m) h) =
      (m : ℝ) ^ 3 * RadialShells.layerMass (R + h) (R + 2 * h) := by
  have hdis : Pairwise (fun i j : Grid m =>
      Disjoint (closedBall (center R i) (R + 2 * h) \ closedBall (center R i) (R + h))
        (closedBall (center R j) (R + 2 * h) \ closedBall (center R j) (R + h))) := by
    intro i j hij
    exact (enlarged_closed_balls_pairwise_disjoint R h hh hR m hij).mono sdiff_subset sdiff_subset
  rw [lattice_outer_second R h hh hR m,
    measureReal_iUnion_fintype hdis (fun _ => measurableSet_closedBall.diff measurableSet_closedBall)
      (fun i => measure_ne_top_of_subset sdiff_subset (closedBall_volume_ne_top (center R i) (R + 2 * h)))]
  simp_rw [closed_closed_shell_volume _ (R + h) (R + 2 * h) (by linarith) (by linarith)]
  simp

theorem lattice_outer_ratio (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R)
    (m : ℕ) (hm : 1 ≤ m) :
    volume.real (outerFirstLayer (latticeBalls R m) h) /
      volume.real (outerSecondLayer (latticeBalls R m) h) =
    RadialShells.layerMass R (R + h) / RadialShells.layerMass (R + h) (R + 2 * h) := by
  rw [lattice_outer_first_volume R h hh.le hR m, lattice_outer_second_volume R h hh.le hR m]
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  exact mul_div_mul_left _ _ (by positivity : (m : ℝ) ^ 3 ≠ 0)

theorem lattice_inner_first_volume (R h : ℝ) (hh : 0 ≤ h) (hR : 4 * h < R) (m : ℕ) :
    volume.real (innerFirstLayer (latticeBalls R m) h) =
      (m : ℝ) ^ 3 * RadialShells.layerMass (R - h) R := by
  have hRpos : 0 < R := by linarith
  have hdis : Pairwise (fun i j : Grid m =>
      Disjoint (ball (center R i) R \ ball (center R i) (R - h))
        (ball (center R j) R \ ball (center R j) (R - h))) := by
    intro i j hij
    exact (lattice_balls_pairwise_disjoint R hRpos.le m hij).mono sdiff_subset sdiff_subset
  rw [lattice_inner_first R h hRpos m,
    measureReal_iUnion_fintype hdis (fun _ => measurableSet_ball.diff measurableSet_ball)
      (fun i => measure_ne_top_of_subset sdiff_subset (ball_volume_ne_top (center R i) R))]
  simp_rw [open_open_shell_volume _ (R - h) R (by linarith) (by linarith)]
  simp

theorem lattice_inner_second_volume (R h : ℝ) (hh : 0 ≤ h) (hR : 4 * h < R) (m : ℕ) :
    volume.real (innerSecondLayer (latticeBalls R m) h) =
      (m : ℝ) ^ 3 * RadialShells.layerMass (R - 2 * h) (R - h) := by
  have hRpos : 0 < R := by linarith
  have hdis : Pairwise (fun i j : Grid m =>
      Disjoint (ball (center R i) (R - h) \ ball (center R i) (R - 2 * h))
        (ball (center R j) (R - h) \ ball (center R j) (R - 2 * h))) := by
    intro i j hij
    apply (lattice_balls_pairwise_disjoint R hRpos.le m hij).mono
    · exact sdiff_subset.trans (ball_subset_ball (by linarith))
    · exact sdiff_subset.trans (ball_subset_ball (by linarith))
  rw [lattice_inner_second R h hh hRpos m,
    measureReal_iUnion_fintype hdis (fun _ => measurableSet_ball.diff measurableSet_ball)
      (fun i => measure_ne_top_of_subset sdiff_subset (ball_volume_ne_top (center R i) (R - h)))]
  simp_rw [open_open_shell_volume _ (R - 2 * h) (R - h) (by linarith) (by linarith)]
  simp

theorem lattice_inner_ratio (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R)
    (m : ℕ) (hm : 1 ≤ m) :
    volume.real (innerFirstLayer (latticeBalls R m) h) /
      volume.real (innerSecondLayer (latticeBalls R m) h) =
    RadialShells.layerMass (R - h) R / RadialShells.layerMass (R - 2 * h) (R - h) := by
  rw [lattice_inner_first_volume R h hh.le hR m, lattice_inner_second_volume R h hh.le hR m]
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  exact mul_div_mul_left _ _ (by positivity : (m : ℝ) ^ 3 ≠ 0)

end Jellium.Domains
