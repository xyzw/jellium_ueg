import Jellium.Lattice

/-! Compact core profiles averaged over the actual cubic lattice. All finite
translation envelopes are constructed from coordinate bounds. Neutrality,
integrability and support of each core are the only profile inputs. -/

open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Pointwise
open Classical

namespace Jellium.ProfileAverage

open Spatial Jellium.Lattice

private instance volume_neg_invariant : IsNegInvariant (volume : Measure Space) where
  neg_eq_self := (LinearIsometryEquiv.neg ℝ (E := Space)).measurePreserving.map_eq

theorem integrable_translated_profile {L : ℝ} (hL : 0 < L)
    {f : Space → ℝ} (hf : Integrable f) (offset : Space) :
    Integrable (fun u => f (offset - u)) (shiftMeasure L) := by
  have hQ : volume (fundamentalCube L) ≠ 0 := by
    rw [volume_fundamentalCube]
    exact pow_ne_zero 3 (by simpa using hL)
  exact (hf.comp_sub_left offset).integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hQ)

/-- The exact full periodic average for any finite envelope containing every
active translate throughout the fundamental cube. -/
theorem full_profile_average {L : ℝ} (hL : 0 < L) (s : Finset LatticeIndex)
    (x c : Space) (f : Space → ℝ) (hf : Integrable f)
    (houtside : ∀ z, z ∉ s → ∀ u ∈ fundamentalCube L,
      f (x - c - latticeShift L z - u) = 0) :
    Integrable (fun u => ∑ z ∈ s, f (x - c - latticeShift L z - u)) (shiftMeasure L) ∧
    (∫ u, ∑ z ∈ s, f (x - c - latticeShift L z - u) ∂shiftMeasure L) =
      (L ^ 3)⁻¹ * ∫ y, f y := by
  let : AddAction LatticeIndex Space := action L
  let : MeasurableConstVAdd LatticeIndex Space := measurable_action L
  let : VAddInvariantMeasure LatticeIndex Space volume := invariant_volume L
  refine ⟨integrable_finsetSum s (fun z _ => integrable_translated_profile hL hf _), ?_⟩
  have havg := Periodic.normalized_finite_translated_periodization
    (fundamental_domain L hL) (measurableSet_fundamentalCube L) f hf s (x - c)
    (by
      intro z hz u hu
      simpa only [vadd_eq, sub_add_eq_sub_sub] using houtside z hz u hu)
  simpa only [shiftMeasure, vadd_eq, sub_add_eq_sub_sub,
    volume_fundamentalCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hL.le] using havg

/-- A single explicit integer box works for all observation points in a
bounded region and every profile in the finite core family. -/
theorem exists_uniform_full_average {ι : Type*} {L X C d : ℝ} (hL : 0 < L)
    (J : Finset ι) (c : ι → Space) (r : ι → ℝ) (f : ι → Space → ℝ)
    (hc : ∀ i ∈ J, ∀ k, |c i k| ≤ C) (hr : ∀ i ∈ J, r i ≤ d)
    (hf : ∀ i ∈ J, Integrable (f i))
    (hsupport : ∀ i ∈ J, Function.support (f i) ⊆ closedBall 0 (r i)) :
    ∃ N : ℤ, ∀ x : Space, (∀ k, |x k| ≤ X) →
      Integrable (fun u => ∑ i ∈ J, ∑ z ∈ latticeEnvelope N,
        f i (x - c i - latticeShift L z - u)) (shiftMeasure L) ∧
      (∫ u, ∑ i ∈ J, ∑ z ∈ latticeEnvelope N,
        f i (x - c i - latticeShift L z - u) ∂shiftMeasure L) =
          (L ^ 3)⁻¹ * ∑ i ∈ J, ∫ y, f i y := by
  obtain ⟨N, hN⟩ := exists_uniform_correction_envelope L X C (L / 2) d hL
  refine ⟨N, fun x hx => ?_⟩
  have havg (i : ι) (hi : i ∈ J) := full_profile_average hL (latticeEnvelope N)
    x (c i) (f i) (hf i hi) (by
      intro z hz u hu
      by_contra hne
      exact hz (hN z x (c i) u (r i) (f i) hx (hc i hi)
        (coord_bound_of_fundamentalCube hu) (hr i hi) (hsupport i hi) hne))
  refine ⟨integrable_finsetSum J (fun i hi => (havg i hi).1), ?_⟩
  rw [integral_finsetSum J (fun i hi => (havg i hi).1), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => (havg i hi).2)

/-- Translated support is the corresponding translated ball. -/
theorem translated_profile_support {r : ℝ} {f : Space → ℝ}
    (hsupport : Function.support f ⊆ closedBall 0 r) (c : Space) :
    Function.support (fun x => f (x - c)) ⊆ closedBall c r := by
  intro x hx
  have hmem := hsupport hx
  simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hmem

/-- Selected profiles are integrable in the translation parameter. The
selection event is proved measurable from the actual cube criterion. -/
theorem integrable_selected_profile {L : ℝ} (hL : 0 < L)
    (R a r : ℝ) (c x : Space) (z : LatticeIndex) (f : Space → ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hf : Integrable f) :
    Integrable (fun u => selectedCorrection (cube R) a (c + latticeShift L z + u)
      r (fun y => f (y - c - latticeShift L z - u)) x) (shiftMeasure L) := by
  have hi := (integrable_translated_profile hL hf (x - c - latticeShift L z)).indicator
    (measurableSet_selectedBall L R a r c z ha hr)
  exact hi

/-- A neutral compact core has exactly zero selected correction average in
the deep bulk. The finite envelope is constructed uniformly on the whole box. -/
theorem exists_selected_neutral_plateau {ι : Type*} {L R a C d ρ₀ : ℝ}
    (hL : 0 < L) (J : Finset ι) (c : ι → Space) (r : ι → ℝ) (f : ι → Space → ℝ)
    (hc : ∀ i ∈ J, ∀ k, |c i k| ≤ C) (hr : ∀ i ∈ J, r i ≤ d)
    (hf : ∀ i ∈ J, Integrable (f i))
    (hsupport : ∀ i ∈ J, Function.support (f i) ⊆ closedBall 0 (r i))
    (hcharge : ∀ i ∈ J, (∫ y, f i y) = 0) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    ∃ N : ℤ, ∀ x ∈ cube (R - 2 * (a + 2 * d)),
      (∫ u, ρ₀ + ∑ i ∈ J, ∑ z ∈ latticeEnvelope N,
        selectedCorrection (cube R) a (c i + latticeShift L z + u) (r i)
          (fun y => f i (y - c i - latticeShift L z - u)) x ∂shiftMeasure L) = ρ₀ := by
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability hL
  obtain ⟨N, hN⟩ := exists_uniform_full_average (X := R / 2) hL J c r f hc hr hf hsupport
  refine ⟨N, fun x hx => ?_⟩
  have hxR : x ∈ cube R := cube_mono (by linarith) hx
  have havg := hN x (fun k => (hxR k).le)
  have heq (u : Space) (i : ι) (hi : i ∈ J) (z : LatticeIndex) :
      selectedCorrection (cube R) a (c i + latticeShift L z + u) (r i)
        (fun y => f i (y - c i - latticeShift L z - u)) x =
          f i (x - c i - latticeShift L z - u) := by
    apply selectedCorrection_eq_of_deep (closedBall_subset_cube hx) (hr i hi)
    simpa only [sub_add_eq_sub_sub] using
      translated_profile_support (hsupport i hi) (c i + latticeShift L z + u)
  have hsum (u : Space) :
      (∑ i ∈ J, ∑ z ∈ latticeEnvelope N,
        selectedCorrection (cube R) a (c i + latticeShift L z + u) (r i)
          (fun y => f i (y - c i - latticeShift L z - u)) x) =
      ∑ i ∈ J, ∑ z ∈ latticeEnvelope N, f i (x - c i - latticeShift L z - u) :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun z _ => heq u i hi z
  simp_rw [hsum]
  rw [integral_add (integrable_const ρ₀) havg.1, havg.2]
  have hz : (∑ i ∈ J, ∫ y, f i y) = 0 := Finset.sum_eq_zero hcharge
  simp [hz]

/-- The plateau also holds for the actual finite family containing all
selected centers. Its envelope need not contain inactive exterior cores. -/
theorem neutral_plateau_of_selected_cover {ι : Type*} {L R a d ρ₀ : ℝ}
    (hL : 0 < L) (J : Finset ι) (s : Finset LatticeIndex)
    (c : ι → Space) (r : ι → ℝ) (f : ι → Space → ℝ)
    (hr : ∀ i ∈ J, r i ≤ d) (hf : ∀ i ∈ J, Integrable (f i))
    (hsupport : ∀ i ∈ J, Function.support (f i) ⊆ closedBall 0 (r i))
    (hcharge : ∀ i ∈ J, (∫ y, f i y) = 0)
    (hcover : ∀ i ∈ J, ∀ z u, u ∈ fundamentalCube L →
      selectedBall (cube R) a (c i + latticeShift L z + u) (r i) → z ∈ s)
    (x : Space) (hx : x ∈ cube (R - 2 * (a + 2 * d))) :
    (∫ u, ρ₀ + ∑ i ∈ J, ∑ z ∈ s,
      selectedCorrection (cube R) a (c i + latticeShift L z + u) (r i)
        (fun y => f i (y - c i - latticeShift L z - u)) x ∂shiftMeasure L) = ρ₀ := by
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability hL
  have hdeep := closedBall_subset_cube hx
  have hsupp (i : ι) (hi : i ∈ J) (z : LatticeIndex) (u : Space) :
      Function.support (fun y => f i (y - c i - latticeShift L z - u)) ⊆
        closedBall (c i + latticeShift L z + u) (r i) := by
    simpa only [sub_add_eq_sub_sub] using
      translated_profile_support (hsupport i hi) (c i + latticeShift L z + u)
  have havg (i : ι) (hi : i ∈ J) := full_profile_average hL s x (c i) (f i) (hf i hi)
    (by
      intro z hz u hu
      by_contra hne
      have hactive : dist x (c i + latticeShift L z + u) ≤ r i := hsupp i hi z u hne
      exact hz (hcover i hi z u hu (selectedBall_of_active hdeep (hr i hi) hactive)))
  have heq (u : Space) :
      (∑ i ∈ J, ∑ z ∈ s,
        selectedCorrection (cube R) a (c i + latticeShift L z + u) (r i)
          (fun y => f i (y - c i - latticeShift L z - u)) x) =
      ∑ i ∈ J, ∑ z ∈ s, f i (x - c i - latticeShift L z - u) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro z _
    exact selectedCorrection_eq_of_deep hdeep (hr i hi) (hsupp i hi z u)
  simp_rw [heq]
  rw [integral_add (integrable_const ρ₀)
    (integrable_finsetSum J (fun i hi => (havg i hi).1)),
    integral_finsetSum J (fun i hi => (havg i hi).1)]
  have hz : (∑ i ∈ J, ∫ u, ∑ z ∈ s, f i (x - c i - latticeShift L z - u)
      ∂shiftMeasure L) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [(havg i hi).2, hcharge i hi, mul_zero]
  simp [hz]

/-- At every observation point the selected average of a nonnegative compact
core is bounded by its full periodic average. No boundary regularity of the
core is needed. -/
theorem selected_profile_average_le {L R a r : ℝ} (hL : 0 < L)
    (s : Finset LatticeIndex) (x c : Space) (f : Space → ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hf : Integrable f) (hnonneg : ∀ y, 0 ≤ f y)
    (hsupport : Function.support f ⊆ closedBall 0 r) :
    (∫ u, ∑ z ∈ s, selectedCorrection (cube R) a (c + latticeShift L z + u) r
      (fun y => f (y - c - latticeShift L z - u)) x ∂shiftMeasure L) ≤
        (L ^ 3)⁻¹ * ∫ y, f y := by
  obtain ⟨N, hN⟩ := exists_uniform_correction_envelope L ‖x‖ ‖c‖ (L / 2) r hL
  let t := s ∪ latticeEnvelope N
  have hx (k : Fin 3) : |x k| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x k
  have hc (k : Fin 3) : |c k| ≤ ‖c‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le c k
  have havg := full_profile_average hL t x c f hf (by
    intro z hz u hu
    by_contra hne
    exact hz (Finset.mem_union_right s (hN z x c u r f hx hc
      (coord_bound_of_fundamentalCube hu) le_rfl hsupport hne)))
  rw [← havg.2]
  apply integral_mono
    (integrable_finsetSum s (fun z _ => integrable_selected_profile hL R a r c x z f ha hr hf))
    havg.1
  intro u
  calc
    _ ≤ ∑ z ∈ s, f (x - c - latticeShift L z - u) :=
      Finset.sum_le_sum (fun z _ => selectedCorrection_le _ _ _ _ _ _ (hnonneg _))
    _ ≤ ∑ z ∈ t, f (x - c - latticeShift L z - u) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => hnonneg _)

/-- The continuum averaged trial density has the uniform core-plus-fluid
bound obtained from the packing fraction. Integrability of every selected
core is proved, and the core integral bound is the actual lattice unfolding. -/
theorem averaged_selected_cores_fluid_le {ι : Type*} {L R a H : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (J : Finset ι) (s : Finset LatticeIndex)
    (c : ι → Space) (r : ι → ℝ) (f : ι → Space → ℝ)
    (hr : ∀ i ∈ J, 0 ≤ r i) (hf : ∀ i ∈ J, Integrable (f i))
    (hnonneg : ∀ i ∈ J, ∀ y, 0 ≤ f i y)
    (hsupport : ∀ i ∈ J, Function.support (f i) ⊆ closedBall 0 (r i))
    (fluid : Space → ℝ) (hfluid : Integrable fluid (shiftMeasure L))
    (hbound : ∀ u, fluid u ≤ H) (x : Space) :
    (∫ u, fluid u + ∑ i ∈ J, ∑ z ∈ s,
      selectedCorrection (cube R) a (c i + latticeShift L z + u) (r i)
        (fun y => f i (y - c i - latticeShift L z - u)) x ∂shiftMeasure L) ≤
      H + (L ^ 3)⁻¹ * ∑ i ∈ J, ∫ y, f i y := by
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability hL
  have hp (i : ι) (hi : i ∈ J) := integrable_finsetSum s
    (fun z _ => integrable_selected_profile hL R a (r i) (c i) x z (f i) ha (hr i hi) (hf i hi))
  rw [integral_add hfluid (integrable_finsetSum J hp), integral_finsetSum J hp,
    Finset.mul_sum]
  apply add_le_add
  · calc
      _ ≤ ∫ _u, H ∂shiftMeasure L := integral_mono hfluid (integrable_const H) hbound
      _ = H := by simp
  · exact Finset.sum_le_sum fun i hi => selected_profile_average_le hL s x (c i)
      (f i) ha (hr i hi) (hf i hi) (hnonneg i hi) (hsupport i hi)

/-- Selected corrections vanish outside the outer cube because the actual
selected closed ball lies in its erosion. -/
theorem selected_profile_vanishes_outside {L R a r : ℝ} (ha : 0 ≤ a)
    (c x u : Space) (z : LatticeIndex) (f : Space → ℝ)
    (hsupport : Function.support f ⊆ closedBall 0 r) (hx : x ∉ cube R) :
    selectedCorrection (cube R) a (c + latticeShift L z + u) r
      (fun y => f (y - c - latticeShift L z - u)) x = 0 := by
  unfold selectedCorrection
  split_ifs with hsel
  · by_contra hne
    have hsupp : Function.support (fun y => f (y - c - latticeShift L z - u)) ⊆
        closedBall (c + latticeShift L z + u) r := by
      simpa only [sub_add_eq_sub_sub] using
        translated_profile_support hsupport (c + latticeShift L z + u)
    exact hx (hsel (hsupp hne) (mem_closedBall_self ha))
  · rfl

end Jellium.ProfileAverage
