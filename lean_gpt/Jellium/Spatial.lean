import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual spatial selection and averaging steps in the compensated collar
construction. The sets, masks and integrals below are defined explicitly.
Only ordinary support, integrability and full-period averaging identities are
inputs. The plateau of the selected family is proved, not assumed. -/

open Set Metric MeasureTheory
open scoped BigOperators

namespace Jellium.Spatial

variable {E : Type*} [PseudoMetricSpace E]

/-- Closed-ball erosion. A selected enlarged ball must lie in this set. -/
def eroded (Ω : Set E) (a : ℝ) : Set E :=
  {x | closedBall x a ⊆ Ω}

def selectedBall (Ω : Set E) (a : ℝ) (center : E) (radius : ℝ) : Prop :=
  closedBall center radius ⊆ eroded Ω a

/-- An enlarged ball that touches a sufficiently deep point is selected. -/
theorem selectedBall_of_active
    {Ω : Set E} {a d r : ℝ} {x c : E}
    (hdeep : closedBall x (a + 2 * d) ⊆ Ω)
    (hr : r ≤ d) (hactive : dist x c ≤ r) :
    selectedBall Ω a c r := by
  intro y hy z hz
  apply hdeep
  simp only [mem_closedBall] at hy hz ⊢
  have hcx : dist c x ≤ r := by simpa only [dist_comm] using hactive
  have htri₁ := dist_triangle z y x
  have htri₂ := dist_triangle y c x
  linarith

noncomputable def selectedCorrection
    (Ω : Set E) (a : ℝ) (c : E) (r : ℝ) (f : E → ℝ) (x : E) : ℝ := by
  classical
  exact if selectedBall Ω a c r then f x else 0

theorem selectedCorrection_eq_of_deep
    {Ω : Set E} {a d r : ℝ} {x c : E} {f : E → ℝ}
    (hdeep : closedBall x (a + 2 * d) ⊆ Ω)
    (hr : r ≤ d)
    (hsupport : Function.support f ⊆ closedBall c r) :
    selectedCorrection Ω a c r f x = f x := by
  classical
  by_cases hx : f x = 0
  · simp [selectedCorrection, hx]
  · have hactive : dist x c ≤ r := hsupport hx
    simp [selectedCorrection, selectedBall_of_active hdeep hr hactive]

/-- Equality with the full family is termwise and therefore also works for a
countable periodic family represented by a `tsum`. -/
theorem selected_tsum_eq_of_deep
    {ι : Type*} {Ω : Set E} {a d : ℝ} {x : E}
    (c : ι → E) (r : ι → ℝ) (f : ι → E → ℝ)
    (hdeep : closedBall x (a + 2 * d) ⊆ Ω)
    (hr : ∀ i, r i ≤ d)
    (hsupport : ∀ i, Function.support (f i) ⊆ closedBall (c i) (r i)) :
    (∑' i, selectedCorrection Ω a (c i) (r i) (f i) x) = ∑' i, f i x := by
  apply tsum_congr
  intro i
  exact selectedCorrection_eq_of_deep hdeep (hr i) (hsupport i)

theorem selected_sum_eq_of_deep
    {ι : Type*} (s : Finset ι) {Ω : Set E} {a d : ℝ} {x : E}
    (c : ι → E) (r : ι → ℝ) (f : ι → E → ℝ)
    (hdeep : closedBall x (a + 2 * d) ⊆ Ω)
    (hr : ∀ i ∈ s, r i ≤ d)
    (hsupport : ∀ i ∈ s, Function.support (f i) ⊆ closedBall (c i) (r i)) :
    (∑ i ∈ s, selectedCorrection Ω a (c i) (r i) (f i) x) =
      ∑ i ∈ s, f i x := by
  apply Finset.sum_congr rfl
  intro i hi
  exact selectedCorrection_eq_of_deep hdeep (hr i hi) (hsupport i hi)

theorem selectedCorrection_nonneg
    (Ω : Set E) (a : ℝ) (c : E) (r : ℝ) (f : E → ℝ) (x : E)
    (hf : 0 ≤ f x) : 0 ≤ selectedCorrection Ω a c r f x := by
  classical
  simp only [selectedCorrection]
  split_ifs <;> linarith

theorem selectedCorrection_le
    (Ω : Set E) (a : ℝ) (c : E) (r : ℝ) (f : E → ℝ) (x : E)
    (hf : 0 ≤ f x) : selectedCorrection Ω a c r f x ≤ f x := by
  classical
  simp only [selectedCorrection]
  split_ifs <;> linarith

abbrev Space := EuclideanSpace ℝ (Fin 3)

def cube (R : ℝ) : Set Space := {x | ∀ k, |x k| < R / 2}

theorem measurableSet_cube (R : ℝ) : MeasurableSet (cube R) := by
  have hsets (k : Fin 3) : MeasurableSet {x : Space | |x k| < R / 2} :=
    (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).abs
      continuous_const).measurableSet
  convert MeasurableSet.iInter hsets using 1
  ext x
  simp only [cube, Set.mem_ofPred_eq, Set.mem_iInter]

theorem cube_mono {R S : ℝ} (hRS : R ≤ S) : cube R ⊆ cube S := by
  intro x hx k
  exact (hx k).trans_le (by linarith)

theorem volume_cube (R : ℝ) : volume (cube R) = ENNReal.ofReal R ^ 3 := by
  have hset : cube R = WithLp.ofLp ⁻¹'
      (Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (-(R / 2)) (R / 2))) := by
    ext x
    simp only [cube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, forall_const, Set.mem_Ioo, abs_lt]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)).nullMeasurableSet,
    Real.volume_pi_Ioo]
  have hwidth : R / 2 - -(R / 2) = R := by ring
  simp [hwidth]

theorem volume_cube_toReal {R : ℝ} (hR : 0 ≤ R) :
    (volume (cube R)).toReal = R ^ 3 := by
  rw [volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR]

theorem volume_cube_ne_top (R : ℝ) : volume (cube R) ≠ ⊤ := by
  rw [volume_cube]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- The actual shell volume is at most `16 R² H` for `0 ≤ H ≤ R/2`. -/
theorem volume_cube_shell_le {R H : ℝ}
    (hH : 0 ≤ H) (hsmall : 2 * H ≤ R) :
    (volume (cube (R + 2 * H) \ cube (R - 2 * H))).toReal ≤ 16 * R ^ 2 * H := by
  have hR : 0 ≤ R := by linarith
  have hsub : cube (R - 2 * H) ⊆ cube (R + 2 * H) := cube_mono (by linarith)
  rw [measure_sdiff hsub (measurableSet_cube _).nullMeasurableSet (volume_cube_ne_top _),
    ENNReal.toReal_sub_of_le (measure_mono hsub) (volume_cube_ne_top _),
    volume_cube_toReal (by linarith), volume_cube_toReal (by linarith)]
  have hsq : 4 * H ^ 2 ≤ R ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 4 * H by positivity)
  nlinarith

theorem abs_coord_sub_le_dist (x y : Space) (k : Fin 3) :
    |x k - y k| ≤ dist x y := by
  simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (x - y) k)

/-- A smaller coordinate cube lies inside the closed-ball erosion of the
larger cube. Strict cube inequalities remove any boundary ambiguity. -/
theorem closedBall_subset_cube {R h : ℝ} {x : Space}
    (hx : x ∈ cube (R - 2 * h)) : closedBall x h ⊆ cube R := by
  intro y hy k
  have hdist : dist y x ≤ h := hy
  have hcoord := abs_coord_sub_le_dist y x k
  have htriangle : |y k| ≤ |y k - x k| + |x k| := by
    simpa only [sub_add_cancel] using abs_add_le (y k - x k) (x k)
  have hxk := hx k
  linarith

theorem selectedBall_of_inner_cube
    {R a d r : ℝ} {x c : Space}
    (hx : x ∈ cube (R - 2 * (a + 2 * d)))
    (hr : r ≤ d) (hactive : dist x c ≤ r) :
    selectedBall (cube R) a c r :=
  selectedBall_of_active (closedBall_subset_cube hx) hr hactive

/-- Exact center criterion for selecting an enlarged ball in a cube. Hence
averaging selected centers reduces to integrating a cube indicator. -/
theorem selectedBall_cube_iff {R a r : ℝ} {c : Space}
    (ha : 0 ≤ a) (hr : 0 ≤ r) :
    selectedBall (cube R) a c r ↔ c ∈ cube (R - 2 * (a + r)) := by
  constructor
  · intro hsel k
    by_cases hc : 0 ≤ c k
    · have hy : c + (PiLp.single 2 k r : Space) ∈ closedBall c r := by
        simp [mem_closedBall, dist_eq_norm, PiLp.norm_single, abs_of_nonneg hr]
      have hz : c + (PiLp.single 2 k r : Space) + (PiLp.single 2 k a : Space) ∈
          closedBall (c + (PiLp.single 2 k r : Space)) a := by
        simp [mem_closedBall, dist_eq_norm, PiLp.norm_single, abs_of_nonneg ha]
      have hk := (hsel hy hz) k
      simp only [PiLp.add_apply, PiLp.single_eq_same] at hk
      rw [abs_of_nonneg hc]
      have hle := le_abs_self (c k + r + a)
      linarith
    · have hy : c + (PiLp.single 2 k (-r) : Space) ∈ closedBall c r := by
        simp [mem_closedBall, dist_eq_norm, PiLp.norm_single, abs_of_nonneg hr]
      have hz : c + (PiLp.single 2 k (-r) : Space) + (PiLp.single 2 k (-a) : Space) ∈
          closedBall (c + (PiLp.single 2 k (-r) : Space)) a := by
        simp [mem_closedBall, dist_eq_norm, PiLp.norm_single, abs_of_nonneg ha]
      have hk := (hsel hy hz) k
      simp only [PiLp.add_apply, PiLp.single_eq_same] at hk
      rw [abs_of_neg (lt_of_not_ge hc)]
      have hle := neg_le_abs (c k + -r + -a)
      linarith
  · intro hc y hy z hz
    apply closedBall_subset_cube hc
    simp only [mem_closedBall] at hy hz ⊢
    have htriangle := dist_triangle z y c
    linarith

abbrev LatticeIndex := Fin 3 → ℤ

def latticeShift (L : ℝ) (z : LatticeIndex) : Space :=
  WithLp.toLp 2 (fun k => L * (z k : ℝ))

noncomputable def latticeEnvelope (N : ℤ) : Finset LatticeIndex :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-N) N)

theorem mem_latticeEnvelope_of_coord_bound {N : ℤ} {z : LatticeIndex}
    (hz : ∀ k, |(z k : ℝ)| ≤ (N : ℝ)) : z ∈ latticeEnvelope N := by
  apply Fintype.mem_piFinset.mpr
  intro k
  apply Finset.mem_Icc.mpr
  have hk := abs_le.mp (hz k)
  constructor
  · exact_mod_cast hk.1
  · exact_mod_cast hk.2

/-- An actual finite integer box contains all lattice indices with a bounded
translated coordinate. This is the lattice-discreteness step needed to replace
periodic infinite sums by finite envelopes. -/
theorem exists_latticeEnvelope (L B : ℝ) (hL : 0 < L) :
    ∃ N : ℤ, ∀ z : LatticeIndex,
      (∀ k, |L * (z k : ℝ)| ≤ B) → z ∈ latticeEnvelope N := by
  obtain ⟨N, hN⟩ := exists_int_gt (B / L)
  refine ⟨N, fun z hz => mem_latticeEnvelope_of_coord_bound fun k => ?_⟩
  have hk := hz k
  rw [abs_mul, abs_of_pos hL] at hk
  have hdiv : |(z k : ℝ)| ≤ B / L := (le_div_iff₀ hL).mpr (by nlinarith)
  exact hdiv.trans hN.le

/-- A correction supported in a fixed-radius ball can only activate indices
in the explicit finite lattice envelope, uniformly over a bounded averaging
cell and bounded observation region. -/
theorem active_lattice_coordinate_bound
    {L r X C U : ℝ} {z : LatticeIndex} {x c u : Space}
    (hx : ∀ k, |x k| ≤ X) (hc : ∀ k, |c k| ≤ C) (hu : ∀ k, |u k| ≤ U)
    (hactive : dist x (c + latticeShift L z + u) ≤ r) :
    ∀ k, |L * (z k : ℝ)| ≤ r + X + C + U := by
  intro k
  have hcoord := abs_coord_sub_le_dist x (c + latticeShift L z + u) k
  have hdist : |x k - (c k + L * (z k : ℝ) + u k)| ≤ r := by
    simpa only [PiLp.add_apply, latticeShift, PiLp.toLp_apply] using hcoord.trans hactive
  have hneg : |c k + L * (z k : ℝ) + u k - x k| ≤ r := by
    simpa only [abs_sub_comm] using hdist
  have h₁ := abs_add_le (c k + L * (z k : ℝ) + u k - x k)
    (x k - c k - u k)
  have h₂ : |x k - c k - u k| ≤ |x k - c k| + |u k| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (x k - c k) (-u k)
  have h₃ : |x k - c k| ≤ |x k| + |c k| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (x k) (-c k)
  have heq : (c k + L * (z k : ℝ) + u k - x k) + (x k - c k - u k) =
      L * (z k : ℝ) := by ring
  rw [heq] at h₁
  linarith [hx k, hc k, hu k]

theorem exists_uniform_correction_envelope
    (L X C U rmax : ℝ) (hL : 0 < L) :
    ∃ N : ℤ, ∀ (z : LatticeIndex) (x c u : Space) (r : ℝ) (f : Space → ℝ),
      (∀ k, |x k| ≤ X) → (∀ k, |c k| ≤ C) → (∀ k, |u k| ≤ U) →
      r ≤ rmax → Function.support f ⊆ closedBall 0 r →
      f (x - c - latticeShift L z - u) ≠ 0 → z ∈ latticeEnvelope N := by
  obtain ⟨N, hN⟩ := exists_latticeEnvelope L (rmax + X + C + U) hL
  refine ⟨N, fun z x c u r f hx hc hu hr hsupp hactive => hN z ?_⟩
  have hdist : dist x (c + latticeShift L z + u) ≤ r := by
    have hmem := hsupp hactive
    simpa only [mem_closedBall, dist_eq_norm, sub_zero, sub_add_eq_sub_sub] using hmem
  intro k
  exact (active_lattice_coordinate_bound hx hc hu hdist k).trans (by linarith)

theorem lattice_coordinate_bound_of_center
    {L A C U : ℝ} {z : LatticeIndex} {c u : Space}
    (hcenter : ∀ k, |(c + latticeShift L z + u) k| ≤ A)
    (hc : ∀ k, |c k| ≤ C) (hu : ∀ k, |u k| ≤ U) :
    ∀ k, |L * (z k : ℝ)| ≤ A + C + U := by
  intro k
  have hcenterk : |c k + L * (z k : ℝ) + u k| ≤ A := hcenter k
  have h₁ := abs_add_le (c k + L * (z k : ℝ) + u k) (-c k - u k)
  have h₂ : |-c k - u k| ≤ |c k| + |u k| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (-c k) (-u k)
  have heq : (c k + L * (z k : ℝ) + u k) + (-c k - u k) = L * (z k : ℝ) := by ring
  rw [heq] at h₁
  linarith [hc k, hu k]

/-- Selected centers in a bounded cube have a single finite lattice envelope
uniform over every translation in a bounded fundamental cell. -/
theorem exists_uniform_selected_envelope (L R C U : ℝ) (hL : 0 < L) :
    ∃ N : ℤ, ∀ (z : LatticeIndex) (c u : Space),
      (∀ k, |c k| ≤ C) → (∀ k, |u k| ≤ U) →
      c + latticeShift L z + u ∈ cube R → z ∈ latticeEnvelope N := by
  obtain ⟨N, hN⟩ := exists_latticeEnvelope L (R / 2 + C + U) hL
  refine ⟨N, fun z c u hc hu hcenter => hN z ?_⟩
  exact lattice_coordinate_bound_of_center (fun k => (hcenter k).le) hc hu

noncomputable def interiorCells {ι : Type*} (s : Finset ι)
    (K : ι → Set Space) (R w : ℝ) : Finset ι := by
  classical
  exact s.filter (fun i => K i ⊆ cube (R - 2 * w))

/-- The full tiling need only cover almost everywhere. Bounded cell diameter
then proves that the union of interior cells covers the smaller cube. -/
theorem interior_union_covers_ae
    {ι : Type*} (s : Finset ι) (D K : ι → Set Space) {R w t : ℝ}
    (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hcover : ∀ᵐ x ∂(volume : Measure Space), x ∈ cube R →
      ∃ i ∈ s, x ∈ D i)
    (hdiam : ∀ i ∈ s, ∀ x ∈ D i, ∀ y ∈ K i, dist y x ≤ t) :
    ∀ᵐ x ∂(volume : Measure Space), x ∈ cube (R - 2 * (w + t)) →
      x ∈ ⋃ i ∈ interiorCells s K R w, D i := by
  classical
  filter_upwards [hcover] with x hx hdeep
  have hxR : x ∈ cube R := cube_mono (by linarith) hdeep
  obtain ⟨i, hi, hix⟩ := hx hxR
  have hdeep' : x ∈ cube ((R - 2 * w) - 2 * t) := by
    have heq : (R - 2 * w) - 2 * t = R - 2 * (w + t) := by ring
    simpa only [heq] using hdeep
  have hint : K i ⊆ cube (R - 2 * w) := by
    intro y hy
    exact closedBall_subset_cube hdeep' (hdiam i hi x hix y hy)
  have himem : i ∈ interiorCells s K R w := by
    simp only [interiorCells, Finset.mem_filter]
    exact ⟨hi, hint⟩
  exact Set.mem_iUnion₂.mpr ⟨i, himem, hix⟩

theorem interior_union_subset
    {ι : Type*} (s : Finset ι) (D K : ι → Set Space) {R w : ℝ}
    (hw : 0 ≤ w) (hDK : ∀ i ∈ s, D i ⊆ K i) :
    (⋃ i ∈ interiorCells s K R w, D i) ⊆ cube R := by
  classical
  intro x hx
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp hx
  have himem : i ∈ s ∧ K i ⊆ cube (R - 2 * w) := by
    simpa only [interiorCells, Finset.mem_filter] using hi
  exact cube_mono (by linarith) (himem.2 (hDK i himem.1 hix))

/-- Genuine tiling data yields the interior-volume estimate. Equal cell
volume, null-measurability, disjointness and covering are geometric inputs,
while the selected-cell count and boundary loss are conclusions. -/
theorem interior_cell_volume_bounds
    {ι : Type*} (s : Finset ι) (D K : ι → Set Space) {R w t v : ℝ}
    (hw : 0 ≤ w) (ht : 0 ≤ t) (hsize : 2 * (w + t) ≤ R)
    (hcover : ∀ᵐ x ∂(volume : Measure Space), x ∈ cube R → ∃ i ∈ s, x ∈ D i)
    (hDK : ∀ i ∈ s, D i ⊆ K i)
    (hdiam : ∀ i ∈ s, ∀ x ∈ D i, ∀ y ∈ K i, dist y x ≤ t)
    (hmeas : ∀ i ∈ s, NullMeasurableSet (D i) volume)
    (hfinite : ∀ i ∈ s, volume (D i) ≠ ⊤)
    (hpair : Set.Pairwise (s : Set ι) (fun i j => AEDisjoint volume (D i) (D j)))
    (hvolume : ∀ i ∈ s, volume.real (D i) = v) :
    (R - 2 * (w + t)) ^ 3 ≤ (interiorCells s K R w).card * v ∧
      (interiorCells s K R w).card * v ≤ R ^ 3 := by
  classical
  let I := interiorCells s K R w
  have hIsub : I ⊆ s := Finset.filter_subset _ _
  have hupper := interior_union_subset s D K (R := R) hw hDK
  have hUfinite : volume (⋃ i ∈ I, D i) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cube_ne_top R) (measure_mono hupper)
  have hUvolume : volume.real (⋃ i ∈ I, D i) = (I.card : ℝ) * v := by
    rw [measureReal_biUnion_finset₀
      (fun i hi j hj hij => hpair (hIsub hi) (hIsub hj) hij)
      (fun i hi => hmeas i (hIsub hi)) (fun i hi => hfinite i (hIsub hi))]
    calc
      ∑ i ∈ I, volume.real (D i) = ∑ _i ∈ I, v :=
        Finset.sum_congr rfl (fun i hi => hvolume i (hIsub hi))
      _ = (I.card : ℝ) * v := by simp
  have hR : 0 ≤ R := by linarith
  have hlo := ENNReal.toReal_mono hUfinite
    (measure_mono_ae (s := cube (R - 2 * (w + t)))
      (t := ⋃ i ∈ I, D i) (interior_union_covers_ae s D K hw ht hcover hdiam))
  have hup := measureReal_mono hupper (volume_cube_ne_top R)
  change _ ≤ volume.real (⋃ i ∈ I, D i) at hlo
  change volume.real (⋃ i ∈ I, D i) ≤ (volume (cube R)).toReal at hup
  rw [hUvolume, volume_cube_toReal (by linarith)] at hlo
  rw [hUvolume, volume_cube_toReal hR] at hup
  exact ⟨hlo, hup⟩

theorem noninterior_product_support
    {K : Set Space} {ξ ρ : Space → ℝ} {R w t : ℝ}
    (ht : 0 ≤ t)
    (hξ : Function.support ξ ⊆ K)
    (hρ : Function.support ρ ⊆ cube (R + 2 * w))
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist y x ≤ t)
    (hnoninterior : ¬ K ⊆ cube (R - 2 * w)) :
    Function.support (fun x => ξ x * ρ x) ⊆
      cube (R + 2 * (w + t)) \ cube (R - 2 * (w + t)) := by
  intro x hx
  have hξx : ξ x ≠ 0 := by intro hz; exact hx (by simp [hz])
  have hρx : ρ x ≠ 0 := by intro hz; exact hx (by simp [hz])
  refine ⟨cube_mono (by linarith) (hρ hρx), ?_⟩
  intro hdeep
  apply hnoninterior
  have hdeep' : x ∈ cube ((R - 2 * w) - 2 * t) := by
    have heq : (R - 2 * w) - 2 * t = R - 2 * (w + t) := by ring
    simpa only [heq] using hdeep
  intro y hy
  exact closedBall_subset_cube hdeep' (hdiam x (hξ hξx) y hy)

section Average

variable {U ι : Type*} [MeasurableSpace U] (μ : Measure U)
  [IsProbabilityMeasure μ]

/-- The actual averaged selected density for a finite envelope of periodic
indices. Finite envelopes follow from lattice discreteness and compact support. -/
noncomputable def averagedSelectedDensity
    (s : Finset ι) (Ω : Set E) (a background : ℝ)
    (c : U → ι → E) (r : ι → ℝ) (f : U → ι → E → ℝ) (x : E) : ℝ :=
  ∫ u, background + ∑ i ∈ s,
    selectedCorrection Ω a (c u i) (r i) (f u i) x ∂μ

/-- Exact bulk plateau after translation averaging. The zero-average input is
the full periodic-family identity, obtainable from lattice unfolding and zero
charge. The selection step and the resulting plateau are proved here. -/
theorem averagedSelectedDensity_eq_background
    (s : Finset ι) {Ω : Set E} {a d background : ℝ}
    (c : U → ι → E) (r : ι → ℝ) (f : U → ι → E → ℝ) {x : E}
    (hdeep : closedBall x (a + 2 * d) ⊆ Ω)
    (hr : ∀ i ∈ s, r i ≤ d)
    (hsupport : ∀ u i, i ∈ s → Function.support (f u i) ⊆ closedBall (c u i) (r i))
    (hintegrable : Integrable (fun u => ∑ i ∈ s, f u i x) μ)
    (hzero : (∫ u, ∑ i ∈ s, f u i x ∂μ) = 0) :
    averagedSelectedDensity μ s Ω a background c r f x = background := by
  have heq (u : U) :
      (∑ i ∈ s, selectedCorrection Ω a (c u i) (r i) (f u i) x) =
        ∑ i ∈ s, f u i x :=
    selected_sum_eq_of_deep s (c u) r (f u) hdeep hr (hsupport u)
  unfold averagedSelectedDensity
  simp_rw [heq]
  rw [integral_add (integrable_const background) hintegrable, hzero]
  simp

/-- Nonnegative cores may be enlarged to the full periodic family before
integration. This is the actual averaged upper bound, with the core average
supplied by the ordinary unfolding identity. -/
theorem averaged_core_fluid_le
    (s : Finset ι) (Ω : Set E) (a : ℝ)
    (c : U → ι → E) (r : ι → ℝ) (σ : U → ι → E → ℝ)
    (fluid : U → ℝ) (x : E) {fluidBound coreAverage : ℝ}
    (hσ : ∀ u i, i ∈ s → 0 ≤ σ u i x)
    (hfluid : ∀ u, fluid u ≤ fluidBound)
    (hselected : Integrable (fun u => fluid u + ∑ i ∈ s,
      selectedCorrection Ω a (c u i) (r i) (σ u i) x) μ)
    (hfull : Integrable (fun u => ∑ i ∈ s, σ u i x) μ)
    (hmass : (∫ u, ∑ i ∈ s, σ u i x ∂μ) = coreAverage) :
    (∫ u, fluid u + ∑ i ∈ s,
      selectedCorrection Ω a (c u i) (r i) (σ u i) x ∂μ) ≤
      fluidBound + coreAverage := by
  calc
    _ ≤ ∫ u, fluidBound + ∑ i ∈ s, σ u i x ∂μ := by
      apply integral_mono hselected ((integrable_const fluidBound).add hfull)
      intro u
      exact add_le_add (hfluid u) (Finset.sum_le_sum fun i hi =>
        selectedCorrection_le Ω a (c u i) (r i) (σ u i) x (hσ u i hi))
    _ = fluidBound + coreAverage := by
      rw [integral_add (integrable_const fluidBound) hfull, hmass]
      simp

end Average

end Jellium.Spatial
