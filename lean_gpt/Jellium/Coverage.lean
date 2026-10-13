import Jellium.Lattice
import Jellium.Localization

/-! Exact averaged coverage of the selected periodic core family. The finite
family is constructed from the actual selection region. Fixed collar widths
then disappear in the normalized thermodynamic limit. -/

open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Pointwise Topology
open Classical

namespace Jellium.Coverage

open Spatial Jellium.Lattice

noncomputable def selectionEnvelope (L R C : ℝ) (hL : 0 < L) : Finset LatticeIndex :=
  latticeEnvelope (Classical.choose (exists_uniform_selected_envelope L R C (L / 2) hL))

theorem selectionEnvelope_contains {L R C a r : ℝ} (hL : 0 < L) (ha : 0 ≤ a)
    (hr : 0 ≤ r) {c u : Space} {z : LatticeIndex}
    (hc : ∀ k, |c k| ≤ C) (hu : u ∈ fundamentalCube L)
    (hsel : selectedBall (cube R) a (c + latticeShift L z + u) r) :
    z ∈ selectionEnvelope L R C hL := by
  apply Classical.choose_spec (exists_uniform_selected_envelope L R C (L / 2) hL)
    z c u hc (coord_bound_of_fundamentalCube hu)
  exact cube_mono (by linarith) ((selectedBall_cube_iff ha hr).mp hsel)

noncomputable def selectedCount (L R a r : ℝ) (c : Space) (s : Finset LatticeIndex) : ℝ :=
  ∫ u, ∑ z ∈ s, if selectedBall (cube R) a (c + latticeShift L z + u) r then 1 else 0
    ∂shiftMeasure L

theorem selectedCount_eq {L R a r : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hsize : 0 ≤ R - 2 * (a + r)) (c : Space) (s : Finset LatticeIndex)
    (hcover : ∀ z u, u ∈ fundamentalCube L →
      selectedBall (cube R) a (c + latticeShift L z + u) r → z ∈ s) :
    selectedCount L R a r c s = (R - 2 * (a + r)) ^ 3 / L ^ 3 := by
  let : AddAction LatticeIndex Space := action L
  let : MeasurableConstVAdd LatticeIndex Space := measurable_action L
  let : VAddInvariantMeasure LatticeIndex Space volume := invariant_volume L
  have houtside : ∀ z, z ∉ s → ∀ u ∈ fundamentalCube L,
      c + (z +ᵥ u) ∉ cube (R - 2 * (a + r)) := by
    intro z hz u hu hmem
    exact hz (hcover z u hu ((selectedBall_cube_iff ha hr).mpr
      (by simpa only [vadd_eq, add_assoc] using hmem)))
  have hcount := Periodic.normalized_selected_count (fundamental_domain L hL)
    (measurableSet_fundamentalCube L) (measurableSet_cube (R - 2 * (a + r)))
    (volume_cube_ne_top _) s c houtside
  have heq : selectedCount L R a r c s =
      ∫ u, ∑ z ∈ s,
        (cube (R - 2 * (a + r))).indicator (fun _ => (1 : ℝ)) (c + (z +ᵥ u))
        ∂shiftMeasure L := by
    unfold selectedCount
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u
    apply Finset.sum_congr rfl
    intro z _
    simp only [Set.indicator_apply, selectedBall_cube_iff ha hr, vadd_eq, add_assoc]
  rw [heq, shiftMeasure, hcount, volume_cube_toReal hsize, volume_fundamentalCube,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hL.le]

/-- Integrating the actual selected-volume sum gives the weighted exact
counts. This supplies the volume term in the averaged finite-state energy. -/
theorem integral_selected_weights {ι : Type*} {L R a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (J : Finset ι) (s : Finset LatticeIndex)
    (c : ι → Space) (r v : ι → ℝ) (hr : ∀ i ∈ J, 0 ≤ r i) :
    (∫ u, ∑ i ∈ J, ∑ z ∈ s,
      if selectedBall (cube R) a (c i + latticeShift L z + u) (r i) then v i else 0
      ∂shiftMeasure L) = ∑ i ∈ J, v i * selectedCount L R a (r i) (c i) s := by
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability hL
  have hp (i : ι) (hi : i ∈ J) (z : LatticeIndex) :
      Integrable (fun u => if selectedBall (cube R) a
        (c i + latticeShift L z + u) (r i) then v i else 0) (shiftMeasure L) :=
    (integrable_const (v i)).indicator (measurableSet_selectedBall L R a (r i) (c i) z ha (hr i hi))
  rw [integral_finsetSum J (fun i hi => integrable_finsetSum s (fun z _ => hp i hi z))]
  apply Finset.sum_congr rfl
  intro i _
  have heq (u : Space) :
      (∑ z ∈ s, if selectedBall (cube R) a (c i + latticeShift L z + u) (r i) then v i else 0) =
      v i * ∑ z ∈ s, if selectedBall (cube R) a
        (c i + latticeShift L z + u) (r i) then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp
  simp_rw [heq]
  exact integral_const_mul (v i) _

theorem shifted_cube_ratio_tendsto (b : ℝ) :
    Tendsto (fun R : ℝ => (R - b) ^ 3 / R ^ 3) atTop (𝓝 1) := by
  have hdiv : Tendsto (fun R : ℝ => b / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun R : ℝ => b * R⁻¹) atTop (𝓝 (b * 0)))
  have h : Tendsto (fun R : ℝ => (1 - b / R) ^ 3) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hdiv).pow 3
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  field_simp [hR.ne']

/-- Coverage of any finite family of fixed cores tends exactly to its packing
fraction. The envelope is the concrete selected-center envelope above. -/
theorem selected_coverage_tendsto {ι : Type*} {L C a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (J : Finset ι) (c : ι → Space) (r v : ι → ℝ)
    (hc : ∀ i ∈ J, ∀ k, |c i k| ≤ C) (hr : ∀ i ∈ J, 0 ≤ r i) :
    Tendsto (fun R : ℝ =>
      (∑ i ∈ J, v i * selectedCount L R a (r i) (c i)
        (selectionEnvelope L R C hL)) / R ^ 3)
      atTop (𝓝 ((∑ i ∈ J, v i) / L ^ 3)) := by
  have hterm (i : ι) (hi : i ∈ J) :
      Tendsto (fun R : ℝ => v i * selectedCount L R a (r i) (c i)
        (selectionEnvelope L R C hL) / R ^ 3)
        atTop (𝓝 (v i / L ^ 3)) := by
    have hlim := (shifted_cube_ratio_tendsto (2 * (a + r i))).const_mul (v i / L ^ 3)
    simp only [mul_one] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (2 * (a + r i))] with R hR
    rw [selectedCount_eq hL ha (hr i hi) (by linarith) _ _
      (fun z u hu hsel => selectionEnvelope_contains hL ha (hr i hi) (hc i hi) hu hsel)]
    ring
  have hsum := tendsto_finsetSum J hterm
  simpa only [← Finset.sum_div] using hsum

end Jellium.Coverage
