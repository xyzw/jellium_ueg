import Jellium.Spatial
import Jellium.Periodic
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Abel

/-! The actual `L ℤ³` translation action and its half-open fundamental cube.
The fundamental-domain property is proved by the unique integer representative
in each coordinate, rather than supplied as a literature hypothesis. -/

open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Pointwise
open Classical

namespace Jellium.Lattice

open Spatial

def shiftHom (L : ℝ) : LatticeIndex →+ Space where
  toFun := latticeShift L
  map_zero' := by ext k; simp [latticeShift]
  map_add' z w := by ext k; simp [latticeShift, mul_add]

abbrev action (L : ℝ) : AddAction LatticeIndex Space :=
  AddAction.compHom Space (shiftHom L)

def fundamentalCube (L : ℝ) : Set Space :=
  {x | ∀ k, -(L / 2) ≤ x k ∧ x k < L / 2}

theorem measurableSet_fundamentalCube (L : ℝ) : MeasurableSet (fundamentalCube L) := by
  have hsets (k : Fin 3) : MeasurableSet {x : Space | -(L / 2) ≤ x k ∧ x k < L / 2} :=
    ((isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k)).measurableSet).inter
      ((isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k) continuous_const).measurableSet)
  convert MeasurableSet.iInter hsets using 1
  ext x
  simp only [fundamentalCube, Set.mem_ofPred_eq, Set.mem_iInter]

theorem volume_fundamentalCube (L : ℝ) :
    volume (fundamentalCube L) = ENNReal.ofReal L ^ 3 := by
  have hset : fundamentalCube L = WithLp.ofLp ⁻¹'
      (Set.pi Set.univ (fun _ : Fin 3 => Set.Ico (-(L / 2)) (L / 2))) := by
    ext x
    simp only [fundamentalCube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, forall_const, Set.mem_Ico]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).nullMeasurableSet,
    Real.volume_pi_Ico]
  have hwidth : L / 2 - -(L / 2) = L := by ring
  simp [hwidth]

theorem cube_subset_fundamentalCube (L : ℝ) : cube L ⊆ fundamentalCube L := by
  intro x hx k
  exact ⟨(abs_lt.mp (hx k)).1.le, (abs_lt.mp (hx k)).2⟩

theorem coord_bound_of_fundamentalCube {L : ℝ} {u : Space}
    (hu : u ∈ fundamentalCube L) : ∀ k, |u k| ≤ L / 2 := by
  intro k
  exact abs_le.mpr ⟨(hu k).1, (hu k).2.le⟩

noncomputable def shiftMeasure (L : ℝ) : Measure Space :=
  Periodic.normalizedRestriction volume (fundamentalCube L)

theorem shiftMeasure_probability {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (shiftMeasure L) := by
  apply Periodic.normalizedRestriction_probability
  · rw [volume_fundamentalCube]
    exact pow_ne_zero 3 (by simpa using hL)
  · rw [volume_fundamentalCube]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

section Action

variable (L : ℝ)

theorem vadd_eq (z : LatticeIndex) (x : Space) :
    letI : AddAction LatticeIndex Space := action L
    z +ᵥ x = latticeShift L z + x := rfl

theorem measurable_action :
    letI : AddAction LatticeIndex Space := action L
    MeasurableConstVAdd LatticeIndex Space := by
  let : AddAction LatticeIndex Space := action L
  constructor
  intro z
  change Measurable (fun x : Space => latticeShift L z + x)
  exact measurable_const.add measurable_id

theorem invariant_volume :
    letI : AddAction LatticeIndex Space := action L
    VAddInvariantMeasure LatticeIndex Space volume := by
  let : AddAction LatticeIndex Space := action L
  constructor
  intro z s hs
  change volume ((fun x : Space => latticeShift L z + x) ⁻¹' s) = volume s
  exact (measurePreserving_add_left volume (latticeShift L z)).measure_preimage hs.nullMeasurableSet

theorem unique_representative (hL : 0 < L) (x : Space) :
    letI : AddAction LatticeIndex Space := action L
    ∃! z : LatticeIndex, z +ᵥ x ∈ fundamentalCube L := by
  let : AddAction LatticeIndex Space := action L
  have hcoord (k : Fin 3) : ∃! n : ℤ,
      x k + (n : ℝ) * L ∈ Ico (-(L / 2)) (L / 2) := by
    have h := existsUnique_add_zsmul_mem_Ico hL (x k) (-(L / 2))
    have heq : -(L / 2) + L = L / 2 := by ring
    simpa only [heq, zsmul_eq_mul] using h
  choose z hz huniq using hcoord
  refine ⟨z, ?_, ?_⟩
  · intro k
    change -(L / 2) ≤ L * (z k : ℝ) + x k ∧ L * (z k : ℝ) + x k < L / 2
    simpa only [Set.mem_Ico, mul_comm, add_comm] using hz k
  · intro w hw
    funext k
    apply huniq k
    have hk := hw k
    change -(L / 2) ≤ L * (w k : ℝ) + x k ∧ L * (w k : ℝ) + x k < L / 2 at hk
    simpa only [Set.mem_Ico, mul_comm, add_comm] using hk

theorem fundamental_domain (hL : 0 < L) :
    letI : AddAction LatticeIndex Space := action L
    IsAddFundamentalDomain LatticeIndex (fundamentalCube L) volume := by
  let : AddAction LatticeIndex Space := action L
  exact IsAddFundamentalDomain.mk' (measurableSet_fundamentalCube L).nullMeasurableSet
    (unique_representative L hL)

theorem translated_cells_disjoint (hL : 0 < L) :
    letI : AddAction LatticeIndex Space := action L
    Pairwise (fun z w : LatticeIndex => Disjoint (z +ᵥ fundamentalCube L) (w +ᵥ fundamentalCube L)) := by
  let : AddAction LatticeIndex Space := action L
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hxz hxw
  have hzm : -z +ᵥ x ∈ fundamentalCube L := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hxz
  have hwm : -w +ᵥ x ∈ fundamentalCube L := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hxw
  have heq : -z = -w := (unique_representative L hL x).unique hzm hwm
  exact hzw (neg_injective heq)

/-- Exact averaged selected-ball count for the actual `L ℤ³` action. The
finite envelope is constructed, and its size may depend on the box and core.
This is sufficient because no estimate depends on the envelope cardinality. -/
theorem exists_exact_selected_count (hL : 0 < L) (R a r : ℝ) (c : Space)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hsize : 0 ≤ R - 2 * (a + r)) :
    ∃ N : ℤ,
      (∫ u, ∑ z ∈ latticeEnvelope N,
        if selectedBall (cube R) a (c + latticeShift L z + u) r then (1 : ℝ) else 0
        ∂shiftMeasure L) = (R - 2 * (a + r)) ^ 3 / L ^ 3 := by
  classical
  let : AddAction LatticeIndex Space := action L
  let : MeasurableConstVAdd LatticeIndex Space := measurable_action L
  let : VAddInvariantMeasure LatticeIndex Space volume := invariant_volume L
  obtain ⟨N, hN⟩ := exists_uniform_selected_envelope L (R - 2 * (a + r)) ‖c‖ (L / 2) hL
  have hc (k : Fin 3) : |c k| ≤ ‖c‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le c k
  have houtside : ∀ z, z ∉ latticeEnvelope N → ∀ u ∈ fundamentalCube L,
      c + (z +ᵥ u) ∉ cube (R - 2 * (a + r)) := by
    intro z hz u hu hmem
    apply hz
    exact hN z c u hc (coord_bound_of_fundamentalCube hu)
      (by simpa only [vadd_eq, add_assoc] using hmem)
  have hcount := Periodic.normalized_selected_count (fundamental_domain L hL)
    (measurableSet_fundamentalCube L) (measurableSet_cube (R - 2 * (a + r)))
    (volume_cube_ne_top _) (latticeEnvelope N) c houtside
  refine ⟨N, ?_⟩
  calc
    _ = ∫ u, ∑ z ∈ latticeEnvelope N,
        (cube (R - 2 * (a + r))).indicator (fun _ => (1 : ℝ)) (c + (z +ᵥ u))
        ∂shiftMeasure L := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      apply Finset.sum_congr rfl
      intro z _
      simp only [Set.indicator_apply, selectedBall_cube_iff ha hr, vadd_eq, add_assoc]
    _ = (volume (cube (R - 2 * (a + r)))).toReal /
        (volume (fundamentalCube L)).toReal := hcount
    _ = (R - 2 * (a + r)) ^ 3 / L ^ 3 := by
      rw [volume_cube_toReal hsize, volume_fundamentalCube,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal hL.le]

/-- The selection indicator is a measurable function of the actual translation. -/
theorem measurableSet_selectedBall (R a r : ℝ) (c : Space) (z : LatticeIndex)
    (ha : 0 ≤ a) (hr : 0 ≤ r) :
    MeasurableSet {u : Space | selectedBall (cube R) a (c + latticeShift L z + u) r} := by
  have heq : {u : Space | selectedBall (cube R) a (c + latticeShift L z + u) r} =
      (fun u : Space => c + latticeShift L z + u) ⁻¹' cube (R - 2 * (a + r)) := by
    ext u
    exact selectedBall_cube_iff ha hr
  rw [heq]
  exact (measurableSet_cube _).preimage (measurable_const.add measurable_id)

/-- Disjoint sets in the fundamental cube remain disjoint under the full
periodic extension, including across different lattice cells. -/
theorem periodic_copies_disjoint {ι : Type*} (hL : 0 < L) (A : ι → Set Space)
    (hinside : ∀ i, A i ⊆ cube L) (hpair : Pairwise (fun i j => Disjoint (A i) (A j)))
    (u : Space) :
    Pairwise (fun iz jw : ι × LatticeIndex =>
      Disjoint ((fun x => x + latticeShift L iz.2 + u) '' A iz.1)
        ((fun x => x + latticeShift L jw.2 + u) '' A jw.1)) := by
  let : AddAction LatticeIndex Space := action L
  intro iz jw hne
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
  by_cases hz : iz.2 = jw.2
  · have hab : a = b := by
      have heq : a + latticeShift L iz.2 + u = b + latticeShift L iz.2 + u := by
        simpa only [hz] using hax.trans hbx.symm
      exact add_right_cancel (add_right_cancel heq)
    have hij : iz.1 ≠ jw.1 := by
      intro hij
      exact hne (Prod.ext hij hz)
    exact Set.disjoint_left.mp (hpair hij) ha (hab.symm ▸ hb)
  · have hza : a + latticeShift L iz.2 ∈ iz.2 +ᵥ fundamentalCube L := by
      apply Set.mem_vadd_set.mpr
      exact ⟨a, cube_subset_fundamentalCube L (hinside iz.1 ha), by simp [vadd_eq, add_comm]⟩
    have hzb : a + latticeShift L iz.2 ∈ jw.2 +ᵥ fundamentalCube L := by
      apply Set.mem_vadd_set.mpr
      refine ⟨b, cube_subset_fundamentalCube L (hinside jw.1 hb), ?_⟩
      have heq := add_right_cancel (hbx.trans hax.symm)
      simpa only [vadd_eq, add_comm] using heq
    exact Set.disjoint_left.mp (translated_cells_disjoint L hL hz) hza hzb

/-- The cube erosion appearing in selection is exactly the smaller cube. -/
theorem eroded_cube_eq (R a : ℝ) (ha : 0 ≤ a) :
    eroded (cube R) a = cube (R - 2 * a) := by
  ext x
  simpa only [selectedBall, closedBall_zero, singleton_subset_iff, add_zero] using
    (selectedBall_cube_iff (c := x) (R := R) ha (show (0 : ℝ) ≤ 0 by rfl))

theorem translated_closedBall (c h u : Space) (r : ℝ) :
    (fun x => x + h + u) '' closedBall c r = closedBall (c + h + u) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_closedBall, dist_add_right] using hy
  · intro hx
    refine ⟨x - u - h, ?_, ?_⟩
    · have heq : x - u - h - c = x - (c + h + u) := by abel
      simpa only [mem_closedBall, dist_eq_norm, heq] using hx
    · abel

/-- Direct closed-ball form of periodic disjointness, ready for the finite
selected BallFamily construction. -/
theorem periodic_closedBalls_disjoint {ι : Type*} (hL : 0 < L)
    (c : ι → Space) (r : ι → ℝ)
    (hinside : ∀ i, closedBall (c i) (r i) ⊆ cube L)
    (hpair : Pairwise fun i j => Disjoint (closedBall (c i) (r i)) (closedBall (c j) (r j)))
    (u : Space) :
    Pairwise fun iz jw : ι × LatticeIndex =>
      Disjoint (closedBall (c iz.1 + latticeShift L iz.2 + u) (r iz.1))
        (closedBall (c jw.1 + latticeShift L jw.2 + u) (r jw.1)) := by
  simpa only [translated_closedBall] using
    periodic_copies_disjoint L hL (fun i => closedBall (c i) (r i)) hinside hpair u

end Action

end Jellium.Lattice
