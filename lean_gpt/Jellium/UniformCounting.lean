import Jellium.UpperCoverage

/-! Uniform counting of the actual selected periodic balls. Moving between
any two shifts in one fundamental cube changes each coordinate by at most L.
Exact translation averages then give finite-box bounds at every shift. -/

open Set MeasureTheory Filter Topology Finset Classical

namespace Jellium.UniformCounting

open Spatial Jellium.Lattice Jellium.UpperCoverage

theorem shiftMeasure_ae_mem (L : ℝ) :
    ∀ᵐ u ∂shiftMeasure L, u ∈ fundamentalCube L := by
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_fundamentalCube L)) _

theorem selected_shift_comparison {L R a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    {c u v : Space} (hu : u ∈ fundamentalCube L) (hv : v ∈ fundamentalCube L)
    (hsel : selectedBall (cube R) a (c + u) r) :
    selectedBall (cube (R + 2 * L)) a (c + v) r := by
  apply (selectedBall_cube_iff ha hr).2
  have hs := (selectedBall_cube_iff ha hr).1 hsel
  intro k
  have hd : |v k - u k| ≤ L := by
    have hu' := coord_bound_of_fundamentalCube hu k
    have hv' := coord_bound_of_fundamentalCube hv k
    have ht := abs_sub (v k) (u k)
    linarith
  have ht := abs_add_le ((c + u) k) (v k - u k)
  have hid : (c + u) k + (v k - u k) = (c + v) k := by simp
  rw [hid] at ht
  have hk := hs k
  linarith

/-- Finite envelopes may differ. Only the geometric selection implication and
nonnegative weights are needed to compare their sums. -/
theorem selectedSum_le_of_selection {m : ℕ} {L R T a : ℝ}
    (s t : Finset LatticeIndex) (center : Fin m → Space) (radius weight : Fin m → ℝ)
    (u v : Space) (hw : ∀ i, 0 ≤ weight i)
    (hsel : ∀ i z, selectedBall (cube R) a (center i + latticeShift L z + u)
      (radius i + 2 * a) → selectedBall (cube T) a
        (center i + latticeShift L z + v) (radius i + 2 * a))
    (ht : ∀ i z, selectedBall (cube T) a (center i + latticeShift L z + v)
      (radius i + 2 * a) → z ∈ t) :
    selectedSum L R a s center radius weight u ≤ selectedSum L T a t center radius weight v := by
  unfold selectedSum
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ∑ z ∈ s, if selectedBall (cube T) a
        (center i + latticeShift L z + v) (radius i + 2 * a) then weight i else 0 := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs with h h'
      · exact le_rfl
      · exact False.elim (h' (hsel i z h))
      · exact hw i
      · exact le_rfl
    _ ≤ ∑ z ∈ s ∪ t, if selectedBall (cube T) a
        (center i + latticeShift L z + v) (radius i + 2 * a) then weight i else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro z _ _
      split_ifs
      · exact hw i
      · exact le_rfl
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro z _ hz
      exact ite_eq_right (fun h => hz (ht i z h))

/-- The uniform upper and lower finite-box volume bounds. The constant d
bounds every radius plus the three collar/smoothing widths. -/
theorem selectedSum_uniform_bounds {m : ℕ} {L C R a d : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (center : Fin m → Space) (radius weight : Fin m → ℝ)
    (hc : ∀ i k, |center i k| ≤ C) (hr : ∀ i, 0 ≤ radius i)
    (hw : ∀ i, 0 ≤ weight i) (hd : ∀ i, radius i + 3 * a ≤ d)
    (_hd0 : 0 ≤ d) (hR : 2 * (d + L) ≤ R)
    (u : Space) (hu : u ∈ fundamentalCube L) :
    ((∑ i, weight i) / L ^ 3) * (R - 2 * (d + L)) ^ 3 ≤
      selectedSum L R a (Coverage.selectionEnvelope L R C hL) center radius weight u ∧
    selectedSum L R a (Coverage.selectionEnvelope L R C hL) center radius weight u ≤
      ((∑ i, weight i) / L ^ 3) * (R + 2 * L) ^ 3 := by
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability hL
  let s := fun T => Coverage.selectionEnvelope L T C hL
  have hrad (i : Fin m) : 0 ≤ radius i + 2 * a := by linarith [hr i]
  have hcover (T : ℝ) (v : Space) (hv : v ∈ fundamentalCube L) (i : Fin m) (z : LatticeIndex)
      (h : selectedBall (cube T) a (center i + latticeShift L z + v) (radius i + 2 * a)) : z ∈ s T :=
    Coverage.selectionEnvelope_contains hL ha (hrad i) (hc i) hv h
  have hint (T : ℝ) := selectedSum_integrable (R := T) hL ha (s T) center radius weight hr
  have hcomp (T : ℝ) (v w : Space) (hv : v ∈ fundamentalCube L) (hw' : w ∈ fundamentalCube L) :
      selectedSum L T a (s T) center radius weight v ≤
        selectedSum L (T + 2 * L) a (s (T + 2 * L)) center radius weight w :=
    selectedSum_le_of_selection _ _ center radius weight v w hw
      (fun i z h => selected_shift_comparison ha (hrad i) hv hw' h)
      (hcover _ w hw')
  have havg (T : ℝ) (hT : 2 * d ≤ T) :
      (∫ v, selectedSum L T a (s T) center radius weight v ∂shiftMeasure L) =
        ∑ i, weight i * (T - 2 * (radius i + 3 * a)) ^ 3 / L ^ 3 :=
    average_coverage_exact hL ha center radius weight hc hr
      (fun i => by linarith [hd i])
  constructor
  · have hpoint : ∀ᵐ v ∂shiftMeasure L,
        selectedSum L (R - 2 * L) a (s (R - 2 * L)) center radius weight v ≤
          selectedSum L R a (s R) center radius weight u := by
      filter_upwards [shiftMeasure_ae_mem L] with v hv
      convert hcomp (R - 2 * L) v u hv hu using 1
      ring_nf
    have hbound := integral_mono_ae (hint (R - 2 * L)) (integrable_const _) hpoint
    rw [integral_const, probReal_univ, one_smul, havg (R - 2 * L) (by linarith)] at hbound
    apply le_trans _ hbound
    rw [Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hp : (R - 2 * (d + L)) ^ 3 ≤ (R - 2 * L - 2 * (radius i + 3 * a)) ^ 3 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith [hd i])
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (hw i)) (pow_pos hL 3).le
    convert hm using 1
    ring
  · have hpoint : ∀ᵐ v ∂shiftMeasure L,
        selectedSum L R a (s R) center radius weight u ≤
          selectedSum L (R + 2 * L) a (s (R + 2 * L)) center radius weight v := by
      filter_upwards [shiftMeasure_ae_mem L] with v hv
      exact hcomp R u v hu hv
    have hbound := integral_mono_ae (integrable_const _) (hint (R + 2 * L)) hpoint
    rw [integral_const, probReal_univ, one_smul, havg (R + 2 * L) (by linarith)] at hbound
    apply hbound.trans
    rw [Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hp : (R + 2 * L - 2 * (radius i + 3 * a)) ^ 3 ≤ (R + 2 * L) ^ 3 := by
      apply pow_le_pow_left₀ (by linarith [hd i]) (by linarith [hr i])
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (hw i)) (pow_pos hL 3).le
    convert hm using 1
    ring

/-- The manuscript's uniform O(R²) count for the actual selection, with an
explicit constant depending only on the fixed packing and collar width. -/
theorem selectedSum_counting_error {m : ℕ} {L C R a d : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (center : Fin m → Space) (radius weight : Fin m → ℝ)
    (hc : ∀ i k, |center i k| ≤ C) (hr : ∀ i, 0 ≤ radius i)
    (hw : ∀ i, 0 ≤ weight i) (hd : ∀ i, radius i + 3 * a ≤ d)
    (hd0 : 0 ≤ d) (hR : 2 * (d + L) ≤ R)
    (hθ : (∑ i, weight i) / L ^ 3 ≤ 1) (u : Space) (hu : u ∈ fundamentalCube L) :
    |selectedSum L R a (Coverage.selectionEnvelope L R C hL) center radius weight u -
      ((∑ i, weight i) / L ^ 3) * R ^ 3| ≤ 26 * (d + L) * R ^ 2 := by
  have hb := selectedSum_uniform_bounds hL ha center radius weight hc hr hw hd hd0 hR u hu
  exact Upper.counting_error_of_cell_bounds hL.le hd0 hR
    (div_nonneg (Finset.sum_nonneg (fun i _ => hw i)) (pow_pos hL 3).le) hθ hb.1 hb.2

/-- In particular the normalized occupied fraction converges uniformly in the
shift. The packing is fixed before R tends to infinity. -/
theorem selectedSum_uniform_convergence {m : ℕ} {L C a d : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (center : Fin m → Space) (radius weight : Fin m → ℝ)
    (hc : ∀ i k, |center i k| ≤ C) (hr : ∀ i, 0 ≤ radius i)
    (hw : ∀ i, 0 ≤ weight i) (hd : ∀ i, radius i + 3 * a ≤ d)
    (hd0 : 0 ≤ d) (hθ : (∑ i, weight i) / L ^ 3 ≤ 1) :
    ∀ η : ℝ, 0 < η → ∀ᶠ R in atTop, ∀ u ∈ fundamentalCube L,
      |selectedSum L R a (Coverage.selectionEnvelope L R C hL) center radius weight u / R ^ 3 -
        (∑ i, weight i) / L ^ 3| < η := by
  intro η hη
  filter_upwards [eventually_gt_atTop (max (2 * (d + L)) (26 * (d + L) / η))] with R hR
  have hRlarge : 2 * (d + L) < R := (le_max_left _ _).trans_lt hR
  have hRpos : 0 < R := by linarith
  have hsmall : 26 * (d + L) / R < η := by
    apply (div_lt_iff₀ hRpos).2
    have ht := (div_lt_iff₀ hη).1 ((le_max_right _ _).trans_lt hR)
    nlinarith
  intro u hu
  have hbound := selectedSum_counting_error hL ha center radius weight hc hr hw hd hd0 hRlarge.le hθ u hu
  have hdiv := div_le_div_of_nonneg_right hbound (pow_pos hRpos 3).le
  have harg : selectedSum L R a (Coverage.selectionEnvelope L R C hL) center radius weight u / R ^ 3 -
      (∑ i, weight i) / L ^ 3 =
      (selectedSum L R a (Coverage.selectionEnvelope L R C hL) center radius weight u -
        ((∑ i, weight i) / L ^ 3) * R ^ 3) / R ^ 3 := by field_simp
  rw [harg, abs_div, abs_of_pos (pow_pos hRpos 3)]
  apply lt_of_le_of_lt hdiv
  have hrate : 26 * (d + L) * R ^ 2 / R ^ 3 = 26 * (d + L) / R := by
    field_simp
  rw [hrate]
  exact hsmall

end Jellium.UniformCounting
