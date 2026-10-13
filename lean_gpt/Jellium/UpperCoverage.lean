import Jellium.Coverage
import Jellium.Upper

/-! Selected volume and surface sums on the actual finite lattice envelope. -/

open MeasureTheory Filter Topology Finset Classical

namespace Jellium.UpperCoverage

open Spatial

noncomputable def selectedSum {m : ℕ} (L R a : ℝ) (s : Finset LatticeIndex)
    (center : Fin m → Space) (radius weight : Fin m → ℝ) (u : Space) : ℝ :=
  ∑ i, ∑ z ∈ s, if selectedBall (cube R) a (center i + latticeShift L z + u)
    (radius i + 2 * a) then weight i else 0

theorem selectedSum_integrable {m : ℕ} {L R a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (s : Finset LatticeIndex)
    (center : Fin m → Space) (radius weight : Fin m → ℝ)
    (hr : ∀ i, 0 ≤ radius i) :
    Integrable (selectedSum L R a s center radius weight) (Lattice.shiftMeasure L) := by
  let : IsProbabilityMeasure (Lattice.shiftMeasure L) := Lattice.shiftMeasure_probability hL
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro z _
  exact (integrable_const (weight i)).indicator
    (Lattice.measurableSet_selectedBall L R a (radius i + 2 * a) (center i) z ha
      (by linarith [hr i]))

theorem selectedSum_abs_le {m : ℕ} (L R a : ℝ) (s : Finset LatticeIndex)
    (center : Fin m → Space) (radius weight : Fin m → ℝ) (u : Space) :
    |selectedSum L R a s center radius weight u| ≤
      ∑ i, ∑ _z ∈ s, |weight i| := by
  unfold selectedSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro z _
  split_ifs
  · exact le_rfl
  · simp

theorem selected_surface_bound {m : ℕ} (L R a : ℝ) (s : Finset LatticeIndex)
    (center : Fin m → Space) (radius : Fin m → ℝ) {κ rmin : ℝ}
    (hκ : 0 < κ) (hrmin : 0 < rmin) (hr : ∀ i, rmin ≤ radius i) (u : Space) :
    selectedSum L R a s center radius (fun i => radius i ^ 2) u ≤
      selectedSum L R a s center radius (fun i => κ * radius i ^ 3) u / (κ * rmin) := by
  apply (le_div_iff₀ (mul_pos hκ hrmin)).2
  unfold selectedSum
  simp only [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro z _
  split_ifs
  · have h := mul_le_mul_of_nonneg_left (hr i) (sq_nonneg (radius i))
    nlinarith [mul_nonneg hκ.le (show 0 ≤ radius i ^ 3 - radius i ^ 2 * rmin by nlinarith)]
  · simp

/-- An exact finite-box formula for the averaged selected volume. This is
the checked replacement for uniform lattice counting in the final proof.
The selection margin is `r + 3 * a` because the collar contributes `2 * a`
and the smoothed background contributes the remaining `a`. -/
theorem average_coverage_exact {m : ℕ} {L C R a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (center : Fin m → Space) (radius weight : Fin m → ℝ)
    (hc : ∀ i k, |center i k| ≤ C) (hr : ∀ i, 0 ≤ radius i)
    (hsize : ∀ i, 0 ≤ R - 2 * (a + (radius i + 2 * a))) :
    (∫ u, selectedSum L R a (Coverage.selectionEnvelope L R C hL)
      center radius weight u ∂Lattice.shiftMeasure L) =
      ∑ i, weight i * (R - 2 * (radius i + 3 * a)) ^ 3 / L ^ 3 := by
  have hrad (i : Fin m) : 0 ≤ radius i + 2 * a := by linarith [hr i]
  have hcover (i : Fin m) (z : LatticeIndex) (u : Space)
      (hu : u ∈ Lattice.fundamentalCube L)
      (hsel : selectedBall (cube R) a (center i + latticeShift L z + u) (radius i + 2 * a)) :
      z ∈ Coverage.selectionEnvelope L R C hL :=
    Coverage.selectionEnvelope_contains hL ha (hrad i) (hc i) hu hsel
  calc
    _ = ∑ i, weight i * Coverage.selectedCount L R a (radius i + 2 * a) (center i)
        (Coverage.selectionEnvelope L R C hL) :=
      Coverage.integral_selected_weights hL ha Finset.univ
        (Coverage.selectionEnvelope L R C hL) center (fun i => radius i + 2 * a) weight
        (fun i _ => hrad i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Coverage.selectedCount_eq hL ha (hrad i) (hsize i) (center i)
        (Coverage.selectionEnvelope L R C hL) (hcover i)]
      ring

theorem average_coverage_tendsto {m : ℕ} {L C a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (center : Fin m → Space) (radius weight : Fin m → ℝ)
    (hc : ∀ i k, |center i k| ≤ C) (hr : ∀ i, 0 ≤ radius i) :
    Tendsto (fun R : ℝ =>
      (∫ u, selectedSum L R a (Coverage.selectionEnvelope L R C hL)
        center radius weight u ∂Lattice.shiftMeasure L) / R ^ 3)
      atTop (𝓝 ((∑ i, weight i) / L ^ 3)) := by
  have h := Coverage.selected_coverage_tendsto hL ha Finset.univ center
    (fun i => radius i + 2 * a) weight (fun i _ => hc i)
    (fun i _ => by linarith [hr i])
  convert h using 1
  funext R
  congr 1
  exact Coverage.integral_selected_weights hL ha Finset.univ
    (Coverage.selectionEnvelope L R C hL) center (fun i => radius i + 2 * a) weight
    (fun i _ => by linarith [hr i])

end Jellium.UpperCoverage
