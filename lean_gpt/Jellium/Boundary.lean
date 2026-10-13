import Jellium.Spatial
import Jellium.Localization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! From actual localized densities and tiling data to the bounded-layer
prelimit estimate. Lieb–Oxford and smeared energy localization are the only
energy inequalities used as inputs. In particular, no boundary estimate or
bounded-layer conclusion is postulated. -/

open Set Metric MeasureTheory Filter Topology
open scoped BigOperators

namespace Jellium.Boundary

open Spatial

/-- Pointwise sum bound for a subfamily of localized densities. The finite
partition only has to sum to one where the original density is nonzero. -/
theorem localized_power_sum_le
    {ι : Type*} (s b : Finset ι) (ξ : ι → Space → ℝ) (ρ : Space → ℝ)
    {B p : ℝ} (hbs : b ⊆ s) (hp : 1 ≤ p)
    (hξ : ∀ i ∈ s, ∀ x, 0 ≤ ξ i x)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ B)
    (hpart : ∀ x, ρ x ≠ 0 → ∑ i ∈ s, ξ i x = 1) (x : Space) :
    ∑ i ∈ b, (ξ i x * ρ x) ^ p ≤ B ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hpne : p ≠ 0 := by linarith
  have hB : 0 ≤ B := (hρ x).1.trans (hρ x).2
  by_cases hx : ρ x = 0
  · simp only [hx, mul_zero, Real.zero_rpow hpne, Finset.sum_const_zero]
    exact Real.rpow_nonneg hB p
  have hsum := Localization.boundary_partition_rpow_sum_le_one s b
    (fun i => ξ i x) hbs (fun i hi => hξ i hi x) (hpart x hx) hp
  calc
    _ = ∑ i ∈ b, (ξ i x) ^ p * (ρ x) ^ p := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Real.mul_rpow (hξ i (hbs hi) x) (hρ x).1
    _ = (∑ i ∈ b, (ξ i x) ^ p) * (ρ x) ^ p := (Finset.sum_mul ..).symm
    _ ≤ 1 * (ρ x) ^ p :=
      mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (hρ x).1 p)
    _ ≤ B ^ p := by simpa only [one_mul] using Real.rpow_le_rpow (hρ x).1 (hρ x).2 hp0

/-- The integrated Lieb–Oxford density term costs only the actual shell
volume. This rules out any dependence on overlap or boundary-cell count. -/
theorem boundary_power_integral_le
    {ι : Type*} (s b : Finset ι) (ξ : ι → Space → ℝ) (ρ : Space → ℝ)
    {B p : ℝ} {W : Set Space} (hbs : b ⊆ s) (hp : 1 ≤ p)
    (hξ : ∀ i ∈ s, ∀ x, 0 ≤ ξ i x)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ B)
    (hpart : ∀ x, ρ x ≠ 0 → ∑ i ∈ s, ξ i x = 1)
    (hsupport : ∀ i ∈ b, Function.support (fun x => ξ i x * ρ x) ⊆ W)
    (hint : ∀ i ∈ b, Integrable (fun x => (ξ i x * ρ x) ^ p) volume)
    (hW : MeasurableSet W) (hWfin : volume W ≠ ⊤) :
    (∑ i ∈ b, ∫ x, (ξ i x * ρ x) ^ p) ≤ B ^ p * volume.real W := by
  classical
  have hpne : p ≠ 0 := by linarith
  have hnonneg (x : Space) : 0 ≤ ∑ i ∈ b, (ξ i x * ρ x) ^ p :=
    Finset.sum_nonneg fun i hi =>
      Real.rpow_nonneg (mul_nonneg (hξ i (hbs hi) x) (hρ x).1) p
  have hpoint (x : Space) :
      (∑ i ∈ b, (ξ i x * ρ x) ^ p) ≤ W.indicator (fun _ => B ^ p) x := by
    by_cases hx : x ∈ W
    · simpa only [Set.indicator_of_mem hx] using
        localized_power_sum_le s b ξ ρ hbs hp hξ hρ hpart x
    · have hzero (i : ι) (hi : i ∈ b) : ξ i x * ρ x = 0 := by
        by_contra hnot
        exact hx (hsupport i hi hnot)
      simp only [Set.indicator_of_notMem hx]
      apply le_of_eq
      exact Finset.sum_eq_zero fun i hi => by rw [hzero i hi, Real.zero_rpow hpne]
  rw [← integral_finsetSum b hint]
  calc
    _ ≤ ∫ x, W.indicator (fun _ => B ^ p) x :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall hnonneg)
        ((integrableOn_const hWfin).integrable_indicator hW)
        (Filter.Eventually.of_forall hpoint)
    _ = B ^ p * volume.real W := by
      rw [integral_indicator_const _ hW]
      simp only [smul_eq_mul, mul_comm]

theorem local_energy_sum_lower_bound
    {ι : Type*} [DecidableEq ι] (s I : Finset ι) (localEnergy integralPower : ι → ℝ)
    {F c shellCost : ℝ} (hIsub : I ⊆ s) (hc : 0 ≤ c)
    (hinterior : ∀ i ∈ I, localEnergy i = F)
    (hLO : ∀ i ∈ s \ I, -c * integralPower i ≤ localEnergy i)
    (hshell : ∑ i ∈ s \ I, integralPower i ≤ shellCost) :
    (I.card : ℝ) * F - c * shellCost ≤ ∑ i ∈ s, localEnergy i := by
  have hsumLO : -c * (∑ i ∈ s \ I, integralPower i) ≤
      ∑ i ∈ s \ I, localEnergy i := by
    simpa only [Finset.mul_sum] using Finset.sum_le_sum hLO
  have hbound := mul_le_mul_of_nonpos_left hshell (show -c ≤ 0 by linarith)
  have hsplit := Finset.sum_sdiff (f := localEnergy) hIsub
  have hsumI : (∑ i ∈ I, localEnergy i) = (I.card : ℝ) * F := by
    rw [Finset.sum_congr rfl hinterior]
    simp
  rw [hsumI] at hsplit
  linarith

/-- Geometric count bounds imply the sign-independent interior loss used in
the final prelimit estimate. -/
theorem interior_energy_lower_bound
    {count R H v F : ℝ} (hv : 0 < v) (hH : 0 ≤ H) (hsize : 2 * H ≤ R)
    (hlower : (R - 2 * H) ^ 3 ≤ count * v) (hupper : count * v ≤ R ^ 3) :
    R ^ 3 * (F / v) - 6 * R ^ 2 * H * (|F| / v) ≤ count * F := by
  have hpoly : R ^ 3 - (R - 2 * H) ^ 3 ≤ 6 * R ^ 2 * H := by
    have hnonneg := mul_nonneg (sq_nonneg H) (show 0 ≤ 3 * R - 2 * H by linarith)
    nlinarith
  exact Localization.interior_count_lower_bound hv hupper (by linarith)

theorem interior_localized_density
    {K : Set Space} {ξ ρ : Space → ℝ} {R w ρ₀ : ℝ}
    (hξsupport : Function.support ξ ⊆ K)
    (hinterior : K ⊆ cube (R - 2 * w))
    (hbulk : ∀ x ∈ cube (R - 2 * w), ρ x = ρ₀) :
    (fun x => ξ x * ρ x) = (fun x => ρ₀ * ξ x) := by
  funext x
  by_cases hx : ξ x = 0
  · simp [hx]
  · rw [hbulk x (hinterior (hξsupport hx))]
    ring

/-- The local sum estimate is derived from actual density cutoffs and tiling
geometry. `hLO` is the standard Lieb–Oxford input and `hcellEnergy` is the
equal-energy consequence of isometric congruence of the smeared tetrahedra.
All boundary loss, counting and signs are established in the proof. -/
theorem local_sum_from_tiling
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (D K : ι → Set Space) (ξ : ι → Space → ℝ) (ρ : Space → ℝ)
    (energy : (Space → ℝ) → ℝ)
    {R w t v ρ₀ F c B p : ℝ}
    (hw : 0 ≤ w) (ht : 0 ≤ t) (hsize : 2 * (w + t) ≤ R)
    (hv : 0 < v) (hc : 0 ≤ c) (hp : 1 ≤ p)
    (hcover : ∀ᵐ x ∂(volume : Measure Space), x ∈ cube R → ∃ i ∈ s, x ∈ D i)
    (hDK : ∀ i ∈ s, D i ⊆ K i)
    (hdiam : ∀ i ∈ s, ∀ x ∈ K i, ∀ y ∈ K i, dist y x ≤ t)
    (hmeas : ∀ i ∈ s, NullMeasurableSet (D i) volume)
    (hfinite : ∀ i ∈ s, volume (D i) ≠ ⊤)
    (hpair : Set.Pairwise (s : Set ι) (fun i j => AEDisjoint volume (D i) (D j)))
    (hvolume : ∀ i ∈ s, volume.real (D i) = v)
    (hξ : ∀ i ∈ s, ∀ x, 0 ≤ ξ i x)
    (hξsupport : ∀ i ∈ s, Function.support (ξ i) ⊆ K i)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ B)
    (hρsupport : Function.support ρ ⊆ cube (R + 2 * w))
    (hbulk : ∀ x ∈ cube (R - 2 * w), ρ x = ρ₀)
    (hpart : ∀ x, ρ x ≠ 0 → ∑ i ∈ s, ξ i x = 1)
    (hint : ∀ i ∈ s, Integrable (fun x => (ξ i x * ρ x) ^ p) volume)
    (hLO : ∀ i ∈ s, -c * (∫ x, (ξ i x * ρ x) ^ p) ≤
      energy (fun x => ξ i x * ρ x))
    (hcellEnergy : ∀ i ∈ s, energy (fun x => ρ₀ * ξ i x) = F) :
    R ^ 3 * (F / v) - R ^ 2 * (w + t) * (6 * (|F| / v) + 16 * c * B ^ p) ≤
      ∑ i ∈ s, energy (fun x => ξ i x * ρ x) := by
  classical
  let I := interiorCells s K R w
  let W := cube (R + 2 * (w + t)) \ cube (R - 2 * (w + t))
  have hIsub : I ⊆ s := Finset.filter_subset _ _
  have hbs : s \ I ⊆ s := Finset.sdiff_subset
  have hH : 0 ≤ w + t := by linarith
  have hcounts := interior_cell_volume_bounds s D K hw ht hsize hcover hDK
    (fun i hi x hx y hy => hdiam i hi x (hDK i hi hx) y hy)
    hmeas hfinite hpair hvolume
  have hinterior : ∀ i ∈ I, energy (fun x => ξ i x * ρ x) = F := by
    intro i hi
    have hmem : i ∈ s ∧ K i ⊆ cube (R - 2 * w) := by
      simpa only [I, interiorCells, Finset.mem_filter] using hi
    rw [interior_localized_density (hξsupport i hmem.1) hmem.2 hbulk]
    exact hcellEnergy i hmem.1
  have hWsupport : ∀ i ∈ s \ I, Function.support (fun x => ξ i x * ρ x) ⊆ W := by
    intro i hi
    have himem := Finset.mem_sdiff.mp hi
    have hnot : ¬ K i ⊆ cube (R - 2 * w) := by
      intro hsub
      exact himem.2 (by simp only [I, interiorCells, Finset.mem_filter]; exact ⟨himem.1, hsub⟩)
    exact noninterior_product_support ht (hξsupport i himem.1) hρsupport
      (hdiam i himem.1) hnot
  have hWmeas : MeasurableSet W := (measurableSet_cube _).diff (measurableSet_cube _)
  have hWfin : volume W ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cube_ne_top _) (measure_mono Set.sdiff_subset)
  have hpower := boundary_power_integral_le s (s \ I) ξ ρ hbs hp hξ hρ hpart
    hWsupport (fun i hi => hint i (hbs hi)) hWmeas hWfin
  have hB : 0 ≤ B := (hρ 0).1.trans (hρ 0).2
  have hBp : 0 ≤ B ^ p := Real.rpow_nonneg hB p
  have hWbound : volume.real W ≤ 16 * R ^ 2 * (w + t) := volume_cube_shell_le hH hsize
  have hpower' : (∑ i ∈ s \ I, ∫ x, (ξ i x * ρ x) ^ p) ≤
      B ^ p * (16 * R ^ 2 * (w + t)) :=
    hpower.trans (mul_le_mul_of_nonneg_left hWbound hBp)
  have hsum := local_energy_sum_lower_bound s I
    (fun i => energy (fun x => ξ i x * ρ x))
    (fun i => ∫ x, (ξ i x * ρ x) ^ p) hIsub hc hinterior
    (fun i hi => hLO i (hbs hi)) hpower'
  have hinteriorBound := interior_energy_lower_bound (count := (I.card : ℝ))
    (F := F) hv hH hsize hcounts.1 hcounts.2
  nlinarith

/-- A uniform local-sum bound can be averaged without changing its constant,
then inserted into the standard smeared localization inequality. -/
theorem averaged_localization_lower_bound
    {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (localSum : U → ℝ) {localBound κ remainder globalEnergy : ℝ}
    (hκ : 0 ≤ κ) (hint : Integrable localSum μ)
    (hbound : ∀ u, localBound ≤ localSum u)
    (hlocalization : κ * (∫ u, localSum u ∂μ) - remainder ≤ globalEnergy) :
    κ * localBound - remainder ≤ globalEnergy := by
  have havg : localBound ≤ ∫ u, localSum u ∂μ := by
    calc
      localBound = ∫ _u, localBound ∂μ := by simp
      _ ≤ ∫ u, localSum u ∂μ := integral_mono (integrable_const _) hint hbound
  have := mul_le_mul_of_nonneg_left havg hκ
  linarith

/-- Ordinary finite-window data supplied by a locally finite smoothed tiling.
The record contains no energy, boundary-volume or asymptotic conclusion. -/
structure WindowTiling (R w t v : ℝ) where
  indices : Finset ℕ
  cells : ℕ → Set Space
  supports : ℕ → Set Space
  cutoff : ℕ → Space → ℝ
  covers : ∀ᵐ x ∂(volume : Measure Space), x ∈ cube R →
    ∃ i ∈ indices, x ∈ cells i
  cell_subset : ∀ i ∈ indices, cells i ⊆ supports i
  diameter : ∀ i ∈ indices, ∀ x ∈ supports i, ∀ y ∈ supports i, dist y x ≤ t
  measurable : ∀ i ∈ indices, NullMeasurableSet (cells i) volume
  finite : ∀ i ∈ indices, volume (cells i) ≠ ⊤
  disjoint : Set.Pairwise (indices : Set ℕ)
    (fun i j => AEDisjoint volume (cells i) (cells j))
  cell_volume : ∀ i ∈ indices, volume.real (cells i) = v
  cutoff_nonneg : ∀ i ∈ indices, ∀ x, 0 ≤ cutoff i x
  cutoff_support : ∀ i ∈ indices, Function.support (cutoff i) ⊆ supports i
  partition : ∀ x ∈ cube (R + 2 * w), ∑ i ∈ indices, cutoff i x = 1

noncomputable def WindowTiling.localSum {R w t v : ℝ}
    (T : WindowTiling R w t v) (energy : (Space → ℝ) → ℝ) (ρ : Space → ℝ) : ℝ :=
  ∑ i ∈ T.indices, energy (fun x => T.cutoff i x * ρ x)

theorem WindowTiling.localSum_lower {R w t v ρ₀ F c B p : ℝ}
    (T : WindowTiling R w t v) (energy : (Space → ℝ) → ℝ) (ρ : Space → ℝ)
    (hw : 0 ≤ w) (ht : 0 ≤ t) (hsize : 2 * (w + t) ≤ R)
    (hv : 0 < v) (hc : 0 ≤ c) (hp : 1 ≤ p)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ B)
    (hρsupport : Function.support ρ ⊆ cube (R + 2 * w))
    (hbulk : ∀ x ∈ cube (R - 2 * w), ρ x = ρ₀)
    (hint : ∀ i ∈ T.indices, Integrable (fun x => (T.cutoff i x * ρ x) ^ p) volume)
    (hLO : ∀ i ∈ T.indices, -c * (∫ x, (T.cutoff i x * ρ x) ^ p) ≤
      energy (fun x => T.cutoff i x * ρ x))
    (hcell : ∀ i ∈ T.indices, energy (fun x => ρ₀ * T.cutoff i x) = F) :
    R ^ 3 * (F / v) - R ^ 2 * (w + t) * (6 * (|F| / v) + 16 * c * B ^ p) ≤
      T.localSum energy ρ :=
  local_sum_from_tiling T.indices T.cells T.supports T.cutoff ρ energy
    hw ht hsize hv hc hp T.covers T.cell_subset T.diameter T.measurable T.finite
    T.disjoint T.cell_volume T.cutoff_nonneg T.cutoff_support hρ hρsupport hbulk
    (fun x hx => T.partition x (hρsupport hx)) hint hLO hcell

/-- The density term appearing in LLS localization is extensive. -/
theorem integral_density_quadratic_le
    {ρ : Space → ℝ} {B R : ℝ}
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ B)
    (hsupport : Function.support ρ ⊆ cube R) :
    (∫ x, ρ x + (ρ x) ^ 2) ≤ (B + B ^ 2) * volume.real (cube R) := by
  classical
  have hB : 0 ≤ B := (hρ 0).1.trans (hρ 0).2
  have hpoint (x : Space) : ρ x + (ρ x) ^ 2 ≤
      (cube R).indicator (fun _ => B + B ^ 2) x := by
    by_cases hx : x ∈ cube R
    · rw [Set.indicator_of_mem hx]
      have hsquare := mul_le_mul (hρ x).2 (hρ x).2 (hρ x).1 hB
      nlinarith [(hρ x).2]
    · have hzero : ρ x = 0 := by
        by_contra hn
        exact hx (hsupport hn)
      simp [hx, hzero]
  calc
    _ ≤ ∫ x, (cube R).indicator (fun _ => B + B ^ 2) x :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => add_nonneg (hρ x).1 (sq_nonneg _))
        ((integrableOn_const (volume_cube_ne_top R)).integrable_indicator (measurableSet_cube R))
        (Filter.Eventually.of_forall hpoint)
    _ = (B + B ^ 2) * volume.real (cube R) := by
      rw [integral_indicator_const _ (measurableSet_cube R)]
      simp only [smul_eq_mul, mul_comm]

/-- Bounded transition layers from genuine smoothed tilings and the standard
LLS/LO energy inequalities. Every geometric and boundary estimate entering the
two-limit argument is derived above. No kinetic-energy bound is assumed. -/
theorem bounded_layer_from_standard_localization
    {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (energy : (Space → ℝ) → ℝ) (ρ : ℝ → Space → ℝ)
    (width diameter cellVolume cellEnergy : ℝ → ℝ)
    (T : ∀ l R, U → WindowTiling R (width R) (diameter l) (cellVolume l))
    {ρ₀ B p c C K ueg : ℝ}
    (hw : ∀ R, 0 ≤ width R) (ht : ∀ l, 0 ≤ diameter l)
    (hv : ∀ l, 0 < cellVolume l) (hc : 0 ≤ c) (hK : 0 ≤ K) (hp : 1 ≤ p)
    (hwidth : Tendsto (fun R => width R / R) atTop (𝓝 0))
    (hcellLimit : Tendsto (fun l => cellEnergy l / cellVolume l) atTop (𝓝 ueg))
    (hρ : ∀ R x, 0 ≤ ρ R x ∧ ρ R x ≤ B)
    (hρsupport : ∀ R, Function.support (ρ R) ⊆ cube (R + 2 * width R))
    (hbulk : ∀ R x, x ∈ cube (R - 2 * width R) → ρ R x = ρ₀)
    (hint : ∀ l R u i, i ∈ (T l R u).indices →
      Integrable (fun x => ((T l R u).cutoff i x * ρ R x) ^ p) volume)
    (hLO : ∀ l R u i, i ∈ (T l R u).indices →
      -c * (∫ x, ((T l R u).cutoff i x * ρ R x) ^ p) ≤
      energy (fun x => (T l R u).cutoff i x * ρ R x))
    (hcell : ∀ l R u i, i ∈ (T l R u).indices →
      energy (fun x => ρ₀ * (T l R u).cutoff i x) = cellEnergy l)
    (haverage : ∀ l R, Integrable (fun u => (T l R u).localSum energy (ρ R)) μ)
    (hLLS : ∀ᶠ l in atTop, ∀ᶠ R in atTop,
      (1 - C / l) * (∫ u, (T l R u).localSum energy (ρ R) ∂μ) -
        K / l * (∫ x, ρ R x + (ρ R x) ^ 2) ≤ energy (ρ R))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R in atTop, ueg - ε ≤ energy (ρ R) / R ^ 3 := by
  let κ : ℝ → ℝ := fun l => 1 - C / l
  let cell : ℝ → ℝ := fun l => cellEnergy l / cellVolume l
  let coef : ℝ → ℝ := fun l => 6 * (|cellEnergy l| / cellVolume l) + 16 * c * B ^ p
  let main : ℝ → ℝ := fun l => κ l * cell l - (8 * K * (B + B ^ 2)) / l
  let error : ℝ → ℝ → ℝ := fun l R =>
    κ l * ((width R + diameter l) / R) * coef l
  have hB : 0 ≤ B := (hρ 0 0).1.trans (hρ 0 0).2
  have hratio (l : ℝ) :
      Tendsto (fun R => (width R + diameter l) / R) atTop (𝓝 0) :=
    Localization.enlarged_boundary_ratio_tendsto hwidth (diameter l)
  have hκ : Tendsto κ atTop (𝓝 1) := Localization.tendsto_localization_factor C
  have hdiv : Tendsto (fun l : ℝ => (8 * K * (B + B ^ 2)) / l) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun l : ℝ => (8 * K * (B + B ^ 2)) * l⁻¹) atTop
          (𝓝 ((8 * K * (B + B ^ 2)) * 0)))
  have hmain : Tendsto main atTop (𝓝 ueg) := by
    simpa only [main, cell, one_mul, sub_zero] using (hκ.mul hcellLimit).sub hdiv
  have herr : ∀ᶠ l in atTop, Tendsto (error l) atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro l
    simpa only [error, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul (hratio l)).mul_const (coef l)
  have hκnonneg : ∀ᶠ l in atTop, 0 ≤ κ l :=
    ((tendsto_order.1 hκ).1 0 zero_lt_one).mono fun _ h => h.le
  apply Localization.two_limit_lower_bound hmain herr _ ε hε
  filter_upwards [hLLS, hκnonneg, eventually_gt_atTop (0 : ℝ)] with l hLLSl hκl hl
  have hsmall : ∀ᶠ R in atTop, (width R + diameter l) / R < (1 / 2 : ℝ) :=
    (tendsto_order.1 (hratio l)).2 _ (by norm_num)
  filter_upwards [hLLSl, hsmall, eventually_gt_atTop (0 : ℝ)] with R hLLSR hsmallR hR
  have hsize : 2 * (width R + diameter l) ≤ R := by
    have := (div_lt_iff₀ hR).mp hsmallR
    linarith
  have huniform (u : U) :
      R ^ 3 * cell l - R ^ 2 * (width R + diameter l) * coef l ≤
        (T l R u).localSum energy (ρ R) :=
    (T l R u).localSum_lower energy (ρ R) (hw R) (ht l) hsize (hv l) hc hp
      (hρ R) (hρsupport R) (hbulk R) (hint l R u) (hLO l R u) (hcell l R u)
  have hpre := averaged_localization_lower_bound μ
    (fun u => (T l R u).localSum energy (ρ R)) hκl (haverage l R) huniform hLLSR
  have hquad := integral_density_quadratic_le (hρ R) (hρsupport R)
  have houter : (R + 2 * width R) ^ 3 ≤ 8 * R ^ 3 := by
    have hmono := pow_le_pow_left₀ (show 0 ≤ R + 2 * width R by linarith [hw R])
      (show R + 2 * width R ≤ 2 * R by linarith [ht l]) 3
    nlinarith
  have hquad' : (∫ x, ρ R x + (ρ R x) ^ 2) ≤ 8 * (B + B ^ 2) * R ^ 3 := by
    change _ ≤ (B + B ^ 2) * (volume (cube (R + 2 * width R))).toReal at hquad
    rw [volume_cube_toReal (by linarith [hw R])] at hquad
    have := mul_le_mul_of_nonneg_left houter (show 0 ≤ B + B ^ 2 by positivity)
    nlinarith
  have hKdiv : 0 ≤ K / l := div_nonneg hK hl.le
  have hscaled := mul_le_mul_of_nonneg_left hquad' hKdiv
  have hterm : K / l * (8 * (B + B ^ 2) * R ^ 3) =
      (8 * K * (B + B ^ 2)) / l * R ^ 3 := by ring
  rw [hterm] at hscaled
  have hE : κ l * (R ^ 3 * cell l - R ^ 2 * (width R + diameter l) * coef l) -
      (8 * K * (B + B ^ 2)) / l * R ^ 3 ≤ energy (ρ R) := by
    dsimp [κ] at hpre ⊢
    linarith
  apply (le_div_iff₀ (pow_pos hR 3)).mpr
  have halgebra : (main l - error l R) * R ^ 3 =
      κ l * (R ^ 3 * cell l - R ^ 2 * (width R + diameter l) * coef l) -
        (8 * K * (B + B ^ 2)) / l * R ^ 3 := by
    dsimp only [main, error]
    field_simp [hR.ne', hl.ne']
    ring
  rw [halgebra]
  exact hE

end Jellium.Boundary
