import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The actual cubic arrays of balls used for canonicalization. -/

open Set Metric Filter Topology
open MeasureTheory
open scoped BigOperators

namespace Jellium.Domains

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Grid (m : ℕ) := Fin 3 → Fin m

noncomputable def center (R : ℝ) {m : ℕ} (i : Grid m) : Space :=
  WithLp.toLp 2 (fun k => 3 * R * (i k).val)

def latticeBalls (R : ℝ) (m : ℕ) : Set Space :=
  ⋃ i : Grid m, Metric.ball (center R i) R

@[simp] theorem grid_card (m : ℕ) : Fintype.card (Grid m) = m ^ 3 := by
  simp [Grid]

theorem center_apply (R : ℝ) {m : ℕ} (i : Grid m) (k : Fin 3) :
    center R i k = 3 * R * (i k).val := rfl

theorem nat_separation (i j : ℕ) (h : i ≠ j) :
    (1 : ℝ) ≤ |(i : ℝ) - j| := by
  rcases lt_or_gt_of_ne h with hij | hji
  · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hji' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- Distinct lattice centers are separated by at least three radii. -/
theorem center_separation (R : ℝ) (hR : 0 ≤ R) {m : ℕ}
    (i j : Grid m) (hij : i ≠ j) :
    3 * R ≤ dist (center R i) (center R j) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := Function.ne_iff.mp hij
  have hval : (i k).val ≠ (j k).val := fun h => hk (Fin.ext h)
  have hn := nat_separation (i k).val (j k).val hval
  have hcoord := PiLp.dist_apply_le (center R i) (center R j) k
  have heq : dist (center R i k) (center R j k) =
      3 * R * |((i k).val : ℝ) - (j k).val| := by
    rw [Real.dist_eq, center_apply, center_apply]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * R)]
  rw [heq] at hcoord
  have hm := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 3 * R)
  linarith

theorem lattice_balls_pairwise_disjoint (R : ℝ) (hR : 0 ≤ R) (m : ℕ) :
    Pairwise (fun i j : Grid m => Disjoint (Metric.ball (center R i) R)
      (Metric.ball (center R j) R)) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  have := center_separation R hR i j hij
  linarith

/-- The supporting balls for every outer double-layer potential are disjoint. -/
theorem enlarged_closed_balls_pairwise_disjoint (R h : ℝ)
    (hh : 0 ≤ h) (hR : 4 * h < R) (m : ℕ) :
    Pairwise (fun i j : Grid m => Disjoint (Metric.closedBall (center R i) (R + 2 * h))
      (Metric.closedBall (center R j) (R + 2 * h))) := by
  intro i j hij
  apply Metric.closedBall_disjoint_closedBall
  have := center_separation R (by linarith) i j hij
  linarith

theorem center_coordinate_bound (R : ℝ) (hR : 0 ≤ R) {m : ℕ}
    (i : Grid m) (k : Fin 3) : 0 ≤ center R i k ∧ center R i k ≤ 3 * R * m := by
  rw [center_apply]
  constructor
  · positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 3 * R)
    exact_mod_cast Nat.le_of_lt (i k).isLt

/-- A uniform enclosing-ball radius, independent of the number of components. -/
theorem center_norm_bound (R : ℝ) (hR : 0 ≤ R) {m : ℕ}
    (i : Grid m) : ‖center R i‖ ≤ 6 * R * m := by
  have hs : ‖center R i‖ ^ 2 ≤ 3 * (3 * R * m) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ k : Fin 3, (center R i k) ^ 2) ≤ ∑ _k : Fin 3, (3 * R * m) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        obtain ⟨hk0, hk⟩ := center_coordinate_bound R hR i k
        nlinarith
      _ = _ := by norm_num
  have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hrm : 0 ≤ R * m := mul_nonneg hR hn
  nlinarith [sq_nonneg (R * (m : ℝ)), norm_nonneg (center R i)]

theorem latticeBalls_subset_enclosing_ball (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hm : 1 ≤ m) :
    latticeBalls R m ⊆ Metric.ball (0 : Space) (7 * R * m) := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hxi : dist x (center R i) < R := hi
  have hnorm := center_norm_bound R (le_of_lt hR) i
  have htriangle := dist_triangle x (center R i) 0
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hRm : R ≤ R * m := by nlinarith
  rw [Metric.mem_ball, dist_zero_right]
  rw [dist_zero_right] at htriangle
  rw [dist_zero_right] at htriangle
  nlinarith

theorem latticeBalls_open (R : ℝ) (m : ℕ) : IsOpen (latticeBalls R m) :=
  isOpen_iUnion (fun _ => Metric.isOpen_ball)

noncomputable def ballVolume (R : ℝ) : ℝ := (Real.pi * 4 / 3) * R ^ 3

theorem ball_volume_real (x : Space) (R : ℝ) (hR : 0 ≤ R) :
    volume.real (Metric.ball x R) = ballVolume R := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  dsimp [ballVolume]
  ring

theorem closedBall_volume_real (x : Space) (R : ℝ) (hR : 0 ≤ R) :
    volume.real (Metric.closedBall x R) = ballVolume R := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_three]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  dsimp [ballVolume]
  ring

theorem latticeBalls_volume (R : ℝ) (hR : 0 ≤ R) (m : ℕ) :
    volume.real (latticeBalls R m) = (m : ℝ) ^ 3 * ballVolume R := by
  unfold latticeBalls
  rw [measureReal_iUnion_fintype (lattice_balls_pairwise_disjoint R hR m)
    (fun _ => measurableSet_ball)]
  simp_rw [ball_volume_real _ R hR]
  simp

/-- This is the uniform ball condition with explicit constant 343. -/
theorem enclosing_ball_volume (R : ℝ) (hR : 0 ≤ R) (m : ℕ) :
    volume.real (Metric.ball (0 : Space) (7 * R * m)) =
      343 * volume.real (latticeBalls R m) := by
  rw [ball_volume_real _ _ (by positivity), latticeBalls_volume R hR]
  dsimp [ballVolume]
  ring

def radialBoundaryShell (x : Space) (R h : ℝ) : Set Space :=
  Metric.closedBall x (R + h) \ Metric.ball x (R - h)

/-- Every point near the domain boundary belongs to a component's radial shell. -/
theorem boundary_layer_subset_shells (R h : ℝ) (hR : 0 < R) (hh : 0 ≤ h) (m : ℕ) :
    Metric.cthickening h (frontier (latticeBalls R m)) ⊆
      ⋃ i : Grid m, radialBoundaryShell (center R i) R h := by
  intro x hx
  rw [isClosed_frontier.cthickening_eq_biUnion_closedBall hh] at hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  have hyclosure : y ∈ closure (latticeBalls R m) := frontier_subset_closure hy
  have hynot : y ∉ latticeBalls R m := by
    have hn : y ∉ interior (latticeBalls R m) := hy.2
    rw [IsOpen.interior_eq (latticeBalls_open R m)] at hn
    exact hn
  rw [latticeBalls, closure_iUnion_of_finite] at hyclosure
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyclosure
  rw [closure_ball _ (ne_of_gt hR)] at hi
  have hyball : y ∉ Metric.ball (center R i) R :=
    fun h => hynot (Set.mem_iUnion.mpr ⟨i, h⟩)
  have hyr : dist y (center R i) = R := by
    exact le_antisymm hi (le_of_not_gt hyball)
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_, ?_⟩
  · have ht := dist_triangle x y (center R i)
    change dist x (center R i) ≤ R + h
    change dist x y ≤ h at hxy
    rw [hyr] at ht
    linarith
  · have ht := dist_triangle y x (center R i)
    change ¬dist x (center R i) < R - h
    change dist x y ≤ h at hxy
    rw [hyr, dist_comm y x] at ht
    linarith

theorem radialBoundaryShell_volume (x : Space) (R h : ℝ)
    (hh : 0 ≤ h) (hR : h ≤ R) :
    volume.real (radialBoundaryShell x R h) = ballVolume (R + h) - ballVolume (R - h) := by
  unfold radialBoundaryShell
  rw [measureReal_sdiff (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by linarith : R - h ≤ R + h))) measurableSet_ball
      (by rw [EuclideanSpace.volume_closedBall_fin_three]
          exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
            ENNReal.ofReal_ne_top)]
  rw [closedBall_volume_real _ _ (by linarith), ball_volume_real _ _ (by linarith)]

theorem radialBoundaryShell_volume_bound (x : Space) (R h : ℝ)
    (hh : 0 ≤ h) (hR : h ≤ R) :
    volume.real (radialBoundaryShell x R h) ≤
      (Real.pi * 4 / 3) * (8 * R ^ 2 * h) := by
  rw [radialBoundaryShell_volume x R h hh hR]
  have hR0 : 0 ≤ R := le_trans hh hR
  have hh2 : h ^ 2 ≤ R ^ 2 := by nlinarith
  have hh3 : h ^ 3 ≤ R ^ 2 * h := by nlinarith [mul_le_mul_of_nonneg_right hh2 hh]
  have hfactor : (R + h) ^ 3 - (R - h) ^ 3 ≤ 8 * R ^ 2 * h := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ Real.pi * 4 / 3)
  dsimp [ballVolume]
  nlinarith

theorem boundary_layer_volume_bound (R h : ℝ) (hh : 0 ≤ h)
    (hR : h ≤ R) (hRpos : 0 < R) (m : ℕ) :
    volume.real (Metric.cthickening h (frontier (latticeBalls R m))) ≤
      (m : ℝ) ^ 3 * (Real.pi * 4 / 3) * (8 * R ^ 2 * h) := by
  have hfinite : volume (⋃ i : Grid m, radialBoundaryShell (center R i) R h) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_iUnion_fintype_le volume _)
    apply ENNReal.sum_lt_top.mpr
    intro i _
    apply lt_of_le_of_lt (measure_mono (Set.sdiff_subset :
      radialBoundaryShell (center R i) R h ⊆ Metric.closedBall (center R i) (R + h)))
    rw [EuclideanSpace.volume_closedBall_fin_three]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
  calc
    _ ≤ volume.real (⋃ i : Grid m, radialBoundaryShell (center R i) R h) :=
      measureReal_mono (boundary_layer_subset_shells R h hRpos hh m) hfinite
    _ ≤ ∑ i : Grid m, volume.real (radialBoundaryShell (center R i) R h) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Grid m, (Real.pi * 4 / 3) * (8 * R ^ 2 * h) := by
      apply Finset.sum_le_sum
      intro i _
      exact radialBoundaryShell_volume_bound _ R h hh hR
    _ = _ := by simp; ring

theorem latticeBalls_volume_pos (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 1 ≤ m) :
    0 < volume.real (latticeBalls R m) := by
  rw [latticeBalls_volume R (le_of_lt hR)]
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  unfold ballVolume
  positivity

theorem normalized_boundary_bound (R h : ℝ) (hh : 0 ≤ h)
    (hR : h ≤ R) (hRpos : 0 < R) (m : ℕ) (hm : 1 ≤ m) :
    volume.real (Metric.cthickening h (frontier (latticeBalls R m))) /
      volume.real (latticeBalls R m) ≤ 8 * h / R := by
  apply (div_le_iff₀ (latticeBalls_volume_pos R hRpos m hm)).2
  calc
    _ ≤ (m : ℝ) ^ 3 * (Real.pi * 4 / 3) * (8 * R ^ 2 * h) :=
      boundary_layer_volume_bound R h hh hR hRpos m
    _ = (8 * h / R) * volume.real (latticeBalls R m) := by
      rw [latticeBalls_volume R (le_of_lt hRpos)]
      dsimp [ballVolume]
      field_simp

/-- The actual geometric Van Hove condition, with no restriction on the growth
of the number of lattice components. -/
theorem lattice_vanHove (R : ℕ → ℝ) (m : ℕ → ℕ)
    (hRpos : ∀ j, 0 < R j) (hm : ∀ j, 1 ≤ m j)
    (hR : Tendsto R atTop atTop) (h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun j =>
      volume.real (Metric.cthickening h (frontier (latticeBalls (R j) (m j)))) /
        volume.real (latticeBalls (R j) (m j))) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ j in atTop, h ≤ R j := (tendsto_atTop.1 hR) h
  have hbound : ∀ᶠ j in atTop,
      volume.real (Metric.cthickening h (frontier (latticeBalls (R j) (m j)))) /
        volume.real (latticeBalls (R j) (m j)) ≤ 8 * h / R j := by
    filter_upwards [hlarge] with j hj
    exact normalized_boundary_bound (R j) h hh hj (hRpos j) (m j) (hm j)
  have hlim : Tendsto (fun j => 8 * h / R j) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hR).const_mul (8 * h)
  apply squeeze_zero' _ hbound hlim
  exact Eventually.of_forall fun j => div_nonneg measureReal_nonneg
    (le_of_lt (latticeBalls_volume_pos (R j) (hRpos j) (m j) (hm j)))

end Jellium.Domains
