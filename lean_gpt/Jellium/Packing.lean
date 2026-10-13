import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Finite neutral sphere packing with collars in an actual Euclidean cube.

The input `VitaliApproximation` is the standard finite separated-ball corollary
of Vitali covering. It contains no integer particle numbers, collar widths,
minimum radii, or dilations. All of those are constructed below. Its separation
margin is obtained by slightly shrinking a finite Vitali subfamily, which
preserves an arbitrarily prescribed strict volume approximation.

The positive coefficient `κ` represents the Euclidean ball volume coefficient
`4 * π / 3`. Keeping it as a parameter separates the standard sphere-volume
formula from the rounding and geometric construction.
-/

open Set Finset

namespace Jellium.Packing

abbrev Space := EuclideanSpace ℝ (Fin 3)

def cube (L : ℝ) : Set Space := {x | ∀ k, |x k| < L / 2}

structure SeparatedFamily where
  count : ℕ
  center : Fin count → Space
  radius : Fin count → ℝ
  margin : ℝ
  margin_pos : 0 < margin
  radius_pos : ∀ i, 0 < radius i
  separation : ∀ i j, i ≠ j → radius i + radius j + margin ≤ dist (center i) (center j)
  boundary : ∀ i k, |center i k| + radius i + margin ≤ 1 / 2

def VitaliApproximation (κ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 →
    ∃ p : SeparatedFamily, 1 - η ≤ ∑ i, κ * p.radius i ^ 3

structure NeutralPacking (ρ κ a rmin ε : ℝ) where
  length : ℝ
  length_pos : 0 < length
  count : ℕ
  center : Fin count → Space
  radius : Fin count → ℝ
  particles : Fin count → ℕ
  radius_min : ∀ i, rmin ≤ radius i
  particles_pos : ∀ i, 0 < particles i
  neutral : ∀ i, ρ * (κ * radius i ^ 3) = particles i
  collars_disjoint : Pairwise fun i j =>
    Disjoint (Metric.closedBall (center i) (radius i + 2 * a))
      (Metric.closedBall (center j) (radius j + 2 * a))
  collars_inside : ∀ i, Metric.closedBall (center i) (radius i + 2 * a) ⊆ cube length
  coverage : 1 - ε ≤ (∑ i, κ * radius i ^ 3) / length ^ 3

noncomputable def roundedRadius (ρ κ R : ℝ) : ℝ :=
  ((⌊ρ * κ * R ^ 3⌋₊ : ℝ) / (ρ * κ)) ^ ((3 : ℝ)⁻¹)

theorem rounded_nonneg {ρ κ R : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    0 ≤ roundedRadius ρ κ R := by
  unfold roundedRadius
  apply Real.rpow_nonneg
  positivity

theorem rounded_cube {ρ κ R : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    roundedRadius ρ κ R ^ 3 = (⌊ρ * κ * R ^ 3⌋₊ : ℝ) / (ρ * κ) := by
  unfold roundedRadius
  exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num : (3 : ℕ) ≠ 0)

theorem rounded_neutral {ρ κ R : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    ρ * (κ * roundedRadius ρ κ R ^ 3) = (⌊ρ * κ * R ^ 3⌋₊ : ℝ) := by
  rw [rounded_cube hρ hκ]
  field_simp

theorem rounded_le {ρ κ R : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) (hR : 0 ≤ R) :
    roundedRadius ρ κ R ≤ R := by
  apply (pow_le_pow_iff_left₀ (rounded_nonneg hρ hκ) hR (by norm_num : (3 : ℕ) ≠ 0)).1
  rw [rounded_cube hρ hκ]
  apply (div_le_iff₀ (mul_pos hρ hκ)).2
  convert Nat.floor_le (show 0 ≤ ρ * κ * R ^ 3 by positivity) using 1
  ring

theorem rounded_large {ρ κ R rmin : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hrmin : 0 ≤ rmin)
    (hR : 1 ≤ R) (hlarge : rmin ^ 3 + 1 / (ρ * κ) ≤ R) :
    rmin ≤ roundedRadius ρ κ R := by
  have hR3 : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num : (3 : ℕ) ≠ 0)
  have hloss := Nat.lt_floor_add_one (ρ * κ * R ^ 3)
  have hinv : (ρ * κ) * (1 / (ρ * κ)) = 1 := by field_simp
  have hfloor : ρ * κ * rmin ^ 3 ≤ (⌊ρ * κ * R ^ 3⌋₊ : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left (le_trans hlarge hR3) (le_of_lt (mul_pos hρ hκ))
    nlinarith
  apply (pow_le_pow_iff_left₀ hrmin (rounded_nonneg hρ hκ) (by norm_num : (3 : ℕ) ≠ 0)).1
  rw [rounded_cube hρ hκ]
  apply (le_div_iff₀ (mul_pos hρ hκ)).2
  nlinarith

theorem rounded_volume_loss {ρ κ R : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    κ * R ^ 3 - 1 / ρ ≤ κ * roundedRadius ρ κ R ^ 3 := by
  have hvolume : κ * roundedRadius ρ κ R ^ 3 =
      (⌊ρ * κ * R ^ 3⌋₊ : ℝ) / ρ := by
    rw [rounded_cube hρ hκ]
    field_simp
  have hf := Nat.lt_floor_add_one (ρ * κ * R ^ 3)
  have hfdiv := (div_lt_div_iff_of_pos_right hρ).2 hf
  have hleft : (ρ * κ * R ^ 3) / ρ = κ * R ^ 3 := by field_simp
  rw [hleft, add_div] at hfdiv
  rw [hvolume]
  linarith

theorem scaled_dist (T : ℝ) (hT : 0 ≤ T) (x y : Space) :
    dist (T • x) (T • y) = T * dist x y := by
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]

theorem collars_disjoint_of_rounding
    (p : SeparatedFamily) {T a : ℝ} (r : Fin p.count → ℝ)
    (hT : 0 < T) (hmargin : 4 * a < T * p.margin)
    (hr : ∀ i, r i ≤ T * p.radius i) :
    Pairwise fun i j =>
      Disjoint (Metric.closedBall (T • p.center i) (r i + 2 * a))
        (Metric.closedBall (T • p.center j) (r j + 2 * a)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  have hi : dist (T • p.center i) x ≤ r i + 2 * a := by
    simpa [Metric.mem_closedBall, dist_comm] using hxi
  have hj : dist x (T • p.center j) ≤ r j + 2 * a := hxj
  have htriangle := dist_triangle (T • p.center i) x (T • p.center j)
  have hsep := mul_le_mul_of_nonneg_left (p.separation i j hij) (le_of_lt hT)
  rw [scaled_dist T (le_of_lt hT)] at htriangle
  linarith [hr i, hr j]

theorem collars_inside_of_rounding
    (p : SeparatedFamily) {T a : ℝ} (r : Fin p.count → ℝ)
    (hT : 0 < T) (ha : 0 ≤ a) (hmargin : 4 * a < T * p.margin)
    (hr : ∀ i, r i ≤ T * p.radius i) :
    ∀ i, Metric.closedBall (T • p.center i) (r i + 2 * a) ⊆ cube T := by
  intro i x hx k
  have hcoord : |x k - (T • p.center i) k| ≤ dist x (T • p.center i) := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x (T • p.center i) k
  have htri : |x k| ≤ |x k - (T • p.center i) k| + |(T • p.center i) k| := by
    simpa only [sub_add_cancel] using
      abs_add_le (x k - (T • p.center i) k) ((T • p.center i) k)
  have hscale : |(T • p.center i) k| = T * |p.center i k| := by
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hT]
  have hbound := mul_le_mul_of_nonneg_left (p.boundary i k) (le_of_lt hT)
  have hball : dist x (T • p.center i) ≤ r i + 2 * a := hx
  rw [hscale] at htri
  linarith [hr i]

/-- One explicit dilation controls every radius, the collar gaps, and the total
integer-rounding loss. It uses a finite sum rather than an asymptotic choice. -/
theorem large_dilation
    (p : SeparatedFamily) {ρ κ ε a rmin : ℝ}
    (hρ : 0 < ρ) (_hκ : 0 < κ) (hε : 0 < ε) (ha : 0 ≤ a) :
    ∃ T : ℝ, 0 < T ∧ 4 * a < T * p.margin ∧
      (∀ i, 1 ≤ T * p.radius i ∧
        rmin ^ 3 + 1 / (ρ * κ) ≤ T * p.radius i) ∧
      (p.count : ℝ) / ρ ≤ ε / 2 * T ^ 3 := by
  let B : ℝ := max 1 (rmin ^ 3 + 1 / (ρ * κ))
  let S : ℝ := ∑ i, B / p.radius i
  have hB : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hS : 0 ≤ S := by
    exact Finset.sum_nonneg (fun i _ => div_nonneg hB (le_of_lt (p.radius_pos i)))
  have hgap_nonneg : 0 ≤ (4 * a + 1) / p.margin :=
    div_nonneg (by linarith) (le_of_lt p.margin_pos)
  have hcount_nonneg : 0 ≤ 2 * (p.count : ℝ) / (ρ * ε) := by positivity
  let T : ℝ := 1 + (4 * a + 1) / p.margin + 2 * (p.count : ℝ) / (ρ * ε) + S
  have hT1 : 1 ≤ T := by dsimp [T]; linarith
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hgap : (4 * a + 1) / p.margin ≤ T := by dsimp [T]; linarith
  have hmargin : 4 * a < T * p.margin := by
    have hmul := (div_le_iff₀ p.margin_pos).1 hgap
    linarith
  have hscales : ∀ i, B ≤ T * p.radius i := by
    intro i
    have hterm : B / p.radius i ≤ S :=
      Finset.single_le_sum (fun j _ => div_nonneg hB (le_of_lt (p.radius_pos j)))
        (Finset.mem_univ i)
    have hST : S ≤ T := by dsimp [T]; linarith
    exact (div_le_iff₀ (p.radius_pos i)).1 (le_trans hterm hST)
  have hlarge : ∀ i, 1 ≤ T * p.radius i ∧
      rmin ^ 3 + 1 / (ρ * κ) ≤ T * p.radius i := by
    intro i
    exact ⟨le_trans (le_max_left _ _) (hscales i),
      le_trans (le_max_right _ _) (hscales i)⟩
  have hloss : (p.count : ℝ) / ρ ≤ ε / 2 * T ^ 3 := by
    have hfrac : 2 * (p.count : ℝ) / (ρ * ε) ≤ T := by dsimp [T]; linarith
    have hTpow : T ≤ T ^ 3 := le_self_pow₀ hT1 (by norm_num : (3 : ℕ) ≠ 0)
    have hmul := (div_le_iff₀ (mul_pos hρ hε)).1 (le_trans hfrac hTpow)
    apply (div_le_iff₀ hρ).2
    nlinarith
  exact ⟨T, hT, hmargin, hlarge, hloss⟩

theorem rounded_coverage
    (p : SeparatedFamily) {ρ κ ε T : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hT : 0 < T)
    (hcovered : 1 - ε / 2 ≤ ∑ i, κ * p.radius i ^ 3)
    (hloss : (p.count : ℝ) / ρ ≤ ε / 2 * T ^ 3) :
    1 - ε ≤ (∑ i, κ * roundedRadius ρ κ (T * p.radius i) ^ 3) / T ^ 3 := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin p.count)))
    (fun i _ => rounded_volume_loss (R := T * p.radius i) hρ hκ)
  have hscaled : (∑ i, κ * (T * p.radius i) ^ 3) =
      T ^ 3 * ∑ i, κ * p.radius i ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hconstant : (∑ _i : Fin p.count, (1 : ℝ) / ρ) = (p.count : ℝ) / ρ := by
    simp [div_eq_mul_inv]
  rw [Finset.sum_sub_distrib, hscaled, hconstant] at hsum
  have hvolume := mul_le_mul_of_nonneg_left hcovered (le_of_lt (pow_pos hT 3))
  apply (le_div_iff₀ (pow_pos hT 3)).2
  nlinarith

/-- The full packing construction. The only covering input is the usual Vitali
approximation by ordinary balls. Integer neutrality, minimum radius, the room
for collars, actual set disjointness and containment, and the final occupied
volume fraction are proved here. -/
theorem exists_neutral_packing
    {ρ κ ε a rmin : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε < 1)
    (ha : 0 ≤ a) (hrmin : 0 < rmin)
    (hvitali : VitaliApproximation κ) :
    Nonempty (NeutralPacking ρ κ a rmin ε) := by
  obtain ⟨p, hp⟩ := hvitali (ε / 2) (by positivity) (by linarith)
  obtain ⟨T, hT, hmargin, hlarge, hloss⟩ := large_dilation p hρ hκ hε ha
  let r : Fin p.count → ℝ := fun i => roundedRadius ρ κ (T * p.radius i)
  have hr : ∀ i, r i ≤ T * p.radius i := by
    intro i
    exact rounded_le hρ hκ (le_of_lt (mul_pos hT (p.radius_pos i)))
  have hr_lower : ∀ i, rmin ≤ r i := by
    intro i
    exact rounded_large hρ hκ (le_of_lt hrmin) (hlarge i).1 (hlarge i).2
  have hneutral : ∀ i, ρ * (κ * r i ^ 3) = (⌊ρ * κ * (T * p.radius i) ^ 3⌋₊ : ℝ) := by
    intro i
    exact rounded_neutral hρ hκ
  have hnpos : ∀ i, 0 < ⌊ρ * κ * (T * p.radius i) ^ 3⌋₊ := by
    intro i
    have hcast : (0 : ℝ) < (⌊ρ * κ * (T * p.radius i) ^ 3⌋₊ : ℝ) := by
      rw [← hneutral i]
      have hri : 0 < r i := lt_of_lt_of_le hrmin (hr_lower i)
      positivity
    exact Nat.cast_pos.mp hcast
  exact ⟨{
    length := T
    length_pos := hT
    count := p.count
    center := fun i => T • p.center i
    radius := r
    particles := fun i => ⌊ρ * κ * (T * p.radius i) ^ 3⌋₊
    radius_min := hr_lower
    particles_pos := hnpos
    neutral := hneutral
    collars_disjoint := collars_disjoint_of_rounding p r hT hmargin hr
    collars_inside := collars_inside_of_rounding p r hT ha hmargin hr
    coverage := rounded_coverage p hρ hκ hT hp hloss
  }⟩

/-- Actual measure additivity gives the upper bound on the occupied fraction.
The only measure inputs are the ordinary ball and cube volume formulas and
finiteness of the cube. -/
theorem coverage_le_one
    {ρ κ ε a rmin : ℝ} (p : NeutralPacking ρ κ a rmin ε) (ha : 0 ≤ a)
    (μ : MeasureTheory.Measure Space)
    (hfinite : μ (cube p.length) ≠ ⊤)
    (hballs : ∀ i, μ.real (Metric.closedBall (p.center i) (p.radius i)) = κ * p.radius i ^ 3)
    (hcube : μ.real (cube p.length) = p.length ^ 3) :
    (∑ i, κ * p.radius i ^ 3) / p.length ^ 3 ≤ 1 := by
  have hsmall : ∀ i, Metric.closedBall (p.center i) (p.radius i) ⊆
      Metric.closedBall (p.center i) (p.radius i + 2 * a) := by
    intro i
    exact Metric.closedBall_subset_closedBall (by linarith)
  have hinside : ∀ i, Metric.closedBall (p.center i) (p.radius i) ⊆ cube p.length :=
    fun i => Set.Subset.trans (hsmall i) (p.collars_inside i)
  have hdisj : Pairwise fun i j => Disjoint
      (Metric.closedBall (p.center i) (p.radius i))
      (Metric.closedBall (p.center j) (p.radius j)) := by
    intro i j hij
    exact (p.collars_disjoint hij).mono (hsmall i) (hsmall j)
  have hsum := MeasureTheory.measureReal_iUnion_fintype (μ := μ) hdisj
    (fun _ => Metric.isClosed_closedBall.measurableSet)
    (fun i => MeasureTheory.measure_ne_top_of_subset (hinside i) hfinite)
  simp_rw [hballs] at hsum
  have hmono := MeasureTheory.measureReal_mono (μ := μ) (iUnion_subset hinside) hfinite
  rw [hsum, hcube] at hmono
  apply (div_le_iff₀ (pow_pos p.length_pos 3)).2
  simpa using hmono

end Jellium.Packing
