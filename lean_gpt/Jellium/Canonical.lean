import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Finite algebra behind the particle-number fluctuation argument.

These results prove the probability and charge algebra, including exchangeability
of actual uniform permutation assignments and continuity of the two pivot
corrections. Constructing physical states, proving approximation of an infinite
sector law by rational laws, and the limiting domain argument remain separate
analytic obligations.
-/

namespace Jellium.Canonical

open scoped BigOperators
open scoped Topology
open Filter

/-- The two tail corrections preserve omitted mass and first moment. -/
theorem tail_correction_constraints (a b t s : ℝ) (hab : a ≠ b) :
    (b * t - s) / (b - a) + (s - a * t) / (b - a) = t ∧
    a * ((b * t - s) / (b - a)) +
      b * ((s - a * t) / (b - a)) = s := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  constructor <;> field_simp <;> ring

/-- Adding the corrections restores both constraints of a truncated law. -/
theorem corrected_constraints (a b t s mass moment n : ℝ)
    (hab : a ≠ b) (hmass : mass = 1 - t) (hmoment : moment = n - s) :
    mass + (b * t - s) / (b - a) + (s - a * t) / (b - a) = 1 ∧
    moment + a * ((b * t - s) / (b - a)) +
      b * ((s - a * t) / (b - a)) = n := by
  obtain ⟨h₁, h₂⟩ := tail_correction_constraints a b t s hab
  constructor <;> linarith

/-- Strictly positive pivot weights survive sufficiently small corrections. -/
theorem corrected_weight_positive (p d : ℝ) (hd : |d| < p) :
    0 < p + d := by
  have := (abs_lt.mp hd).1
  linarith

/-- Both tail corrections vanish when the omitted mass and first moment vanish. -/
theorem tail_corrections_tendsto_zero {α : Type*} {l : Filter α}
    (a b : ℝ) (t s : α → ℝ)
    (ht : Tendsto t l (𝓝 0)) (hs : Tendsto s l (𝓝 0)) :
    Tendsto (fun k => (b * t k - s k) / (b - a)) l (𝓝 0) ∧
    Tendsto (fun k => (s k - a * t k) / (b - a)) l (𝓝 0) := by
  constructor
  · simpa using ((ht.const_mul b).sub hs).div_const (b - a)
  · simpa using (hs.sub (ht.const_mul a)).div_const (b - a)

/-- Thus the two strictly positive pivot weights remain positive eventually. -/
theorem tail_corrected_weights_eventually_positive {α : Type*} {l : Filter α}
    (a b pa pb : ℝ) (t s : α → ℝ) (hpa : 0 < pa) (hpb : 0 < pb)
    (ht : Tendsto t l (𝓝 0)) (hs : Tendsto s l (𝓝 0)) :
    ∀ᶠ k in l, 0 < pa + (b * t k - s k) / (b - a) ∧
      0 < pb + (s k - a * t k) / (b - a) := by
  obtain ⟨ha, hb⟩ := tail_corrections_tendsto_zero a b t s ht hs
  have hla : Tendsto (fun k => pa + (b * t k - s k) / (b - a)) l (𝓝 pa) := by
    simpa using ha.const_add pa
  have hlb : Tendsto (fun k => pb + (s k - a * t k) / (b - a)) l (𝓝 pb) := by
    simpa using hb.const_add pb
  exact (Filter.Tendsto.eventually_const_lt hpa hla).and
    (Filter.Tendsto.eventually_const_lt hpb hlb)

/-- Perturbing the retained non-pivot mass and moment continuously perturbs the
two reconstructed pivots. This is the continuity step in rational approximation. -/
theorem reconstructed_pivots_tendsto {α : Type*} {l : Filter α}
    (a b n m z : ℝ) (mass firstMoment : α → ℝ)
    (hm : Tendsto mass l (𝓝 m)) (hz : Tendsto firstMoment l (𝓝 z)) :
    let qb := (n - a - (z - a * m)) / (b - a)
    let qa := 1 - qb - m
    Tendsto (fun k => (n - a - (firstMoment k - a * mass k)) / (b - a))
      l (𝓝 qb) ∧
    Tendsto (fun k => 1 -
      (n - a - (firstMoment k - a * mass k)) / (b - a) - mass k)
      l (𝓝 qa) := by
  dsimp
  have hb := ((hz.sub (hm.const_mul a)).const_sub (n - a)).div_const (b - a)
  exact ⟨hb, (hb.const_sub 1).sub hm⟩

/-- Positivity is retained for sufficiently accurate pivot reconstruction. -/
theorem reconstructed_pivots_eventually_positive {α : Type*} {l : Filter α}
    (a b n m z : ℝ) (mass firstMoment : α → ℝ)
    (hm : Tendsto mass l (𝓝 m)) (hz : Tendsto firstMoment l (𝓝 z))
    (hb : 0 < (n - a - (z - a * m)) / (b - a))
    (ha : 0 < 1 - (n - a - (z - a * m)) / (b - a) - m) :
    ∀ᶠ k in l,
      0 < (n - a - (firstMoment k - a * mass k)) / (b - a) ∧
      0 < 1 - (n - a - (firstMoment k - a * mass k)) / (b - a) - mass k := by
  obtain ⟨hlb, hla⟩ := reconstructed_pivots_tendsto a b n m z mass firstMoment hm hz
  exact (Filter.Tendsto.eventually_const_lt hb hlb).and
    (Filter.Tendsto.eventually_const_lt ha hla)

/-- Rational pivot reconstruction really has rational values and exact constraints.
The other weights contribute `mass` and `moment` to the two sums. -/
theorem rational_pivot_constraints (a b n mass moment : ℚ) (hab : a ≠ b) :
    let qb := (n - a - (moment - a * mass)) / (b - a)
    let qa := 1 - qb - mass
    qa + qb + mass = 1 ∧ a * qa + b * qb + moment = n := by
  dsimp
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  constructor
  · ring
  · field_simp
    ring

section FiniteAssignments

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]

/-- The finite second moment for assignment weights `p` and ball charges `Q`. -/
def moment (p : A → ℝ) (Q : A → I → ℝ) (i j : I) : ℝ :=
  ∑ ω, p ω * (Q ω i * Q ω j)

omit [DecidableEq I] in
/-- Exact neutrality of each assignment makes every row sum of second moments zero. -/
theorem moment_row_sum_zero (p : A → ℝ) (Q : A → I → ℝ)
    (hneutral : ∀ ω, ∑ j, Q ω j = 0) (i : I) :
    ∑ j, moment p Q i j = 0 := by
  unfold moment
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro ω _
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum, hneutral ω, mul_zero]

omit [Fintype I] [DecidableEq I] in
/-- The diagonal second moment is nonnegative for nonnegative assignment weights. -/
theorem moment_diagonal_nonnegative (p : A → ℝ) (Q : A → I → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (i : I) : 0 ≤ moment p Q i i := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hp ω) (mul_self_nonneg (Q ω i))

/-- Exchangeable second moments and exact neutrality determine the covariance.
This is the identity at manuscript lines 1032–1040. Normalization of `p` is
unnecessary for this algebraic result. -/
theorem exchangeable_covariance (p : A → ℝ) (Q : A → I → ℝ)
    (hneutral : ∀ ω, ∑ j, Q ω j = 0)
    (hcard : 1 < Fintype.card I) (i : I) (v c : ℝ)
    (hdiag : moment p Q i i = v)
    (hoff : ∀ j, j ≠ i → moment p Q i j = c) :
    c = -v / ((Fintype.card I : ℝ) - 1) := by
  have hrow := moment_row_sum_zero p Q hneutral i
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset I)
    (fun j => moment p Q i j) (Finset.mem_univ i)
  have herase : (∑ j ∈ (Finset.univ : Finset I).erase i, moment p Q i j) =
      ((Fintype.card I : ℝ) - 1) * c := by
    calc
      _ = ∑ _j ∈ (Finset.univ : Finset I).erase i, c := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hoff j (Finset.ne_of_mem_erase hj)
      _ = ((Fintype.card I : ℝ) - 1) * c := by
        simp [Finset.card_erase_of_mem, Nat.cast_sub (Nat.le_of_lt hcard)]
  rw [hdiag, herase, hrow] at hsplit
  have hden : (Fintype.card I : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card I := by exact_mod_cast hcard
    linarith
  apply (eq_div_iff hden).2
  nlinarith [hsplit]

/-- Every off-diagonal moment is nonpositive under exchangeability and neutrality. -/
theorem exchangeable_covariance_nonpositive (p : A → ℝ) (Q : A → I → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hneutral : ∀ ω, ∑ j, Q ω j = 0)
    (hcard : 1 < Fintype.card I) (i : I) (v c : ℝ)
    (hdiag : moment p Q i i = v)
    (hoff : ∀ j, j ≠ i → moment p Q i j = c) : c ≤ 0 := by
  rw [exchangeable_covariance p Q hneutral hcard i v c hdiag hoff]
  apply div_nonpos_of_nonpos_of_nonneg
  · have hv := moment_diagonal_nonnegative p Q hp i
    rw [hdiag] at hv
    linarith
  · have : (1 : ℝ) < Fintype.card I := by exact_mod_cast hcard
    linarith

omit [Fintype I] [DecidableEq I] in
/-- Positive Coulomb distance weights preserve the sign of the cross interaction.
`pairs` may be the unordered pairs of distinct balls. -/
theorem cross_interaction_nonpositive (p : A → ℝ) (Q : A → I → ℝ)
    (pairs : Finset (I × I)) (w : I × I → ℝ)
    (hw : ∀ ij ∈ pairs, 0 ≤ w ij)
    (hmoment : ∀ ij ∈ pairs, moment p Q ij.1 ij.2 ≤ 0) :
    ∑ ij ∈ pairs, w ij * moment p Q ij.1 ij.2 ≤ 0 := by
  apply Finset.sum_nonpos
  intro ij hij
  exact mul_nonpos_of_nonneg_of_nonpos (hw ij hij) (hmoment ij hij)

omit [Fintype I] [DecidableEq I] in
/-- Averaging the full finite cross energy is exactly the sum of its moments. -/
theorem average_cross_interaction (p : A → ℝ) (Q : A → I → ℝ)
    (pairs : Finset (I × I)) (w : I × I → ℝ) :
    (∑ ω, p ω * ∑ ij ∈ pairs, w ij * (Q ω ij.1 * Q ω ij.2)) =
      ∑ ij ∈ pairs, w ij * moment p Q ij.1 ij.2 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij _
  unfold moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

omit [Fintype I] [DecidableEq I] in
/-- Therefore adding the averaged cross energy cannot raise the summed local energy. -/
theorem canonical_energy_comparison (p : A → ℝ) (Q : A → I → ℝ)
    (pairs : Finset (I × I)) (w : I × I → ℝ) (localEnergy : ℝ)
    (hw : ∀ ij ∈ pairs, 0 ≤ w ij)
    (hmoment : ∀ ij ∈ pairs, moment p Q ij.1 ij.2 ≤ 0) :
    localEnergy +
      (∑ ω, p ω * ∑ ij ∈ pairs, w ij * (Q ω ij.1 * Q ω ij.2)) ≤
      localEnergy := by
  rw [average_cross_interaction]
  exact add_le_of_nonpos_right (cross_interaction_nonpositive p Q pairs w hw hmoment)

end FiniteAssignments

section PermutationAssignments

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Uniform weights on all permutations of a prescribed finite charge list. -/
noncomputable def permutationWeight (_σ : Equiv.Perm I) : ℝ :=
  (Fintype.card (Equiv.Perm I) : ℝ)⁻¹

/-- Permuting the charge list is exactly an assignment with fixed multiplicities. -/
def permutationCharge (q : I → ℝ) (σ : Equiv.Perm I) (i : I) : ℝ := q (σ i)

theorem permutationWeight_nonnegative (σ : Equiv.Perm I) :
    0 ≤ permutationWeight σ := by
  unfold permutationWeight
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem permutationWeight_normalized :
    ∑ σ : Equiv.Perm I, permutationWeight σ = 1 := by
  unfold permutationWeight
  have hcard : (Fintype.card (Equiv.Perm I) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

/-- A uniform permutation gives the same average at every position. -/
theorem permutation_average_position (x : I → ℝ) (i j : I) :
    (∑ σ : Equiv.Perm I, permutationWeight σ * x (σ i)) =
      ∑ σ : Equiv.Perm I, permutationWeight σ * x (σ j) := by
  unfold permutationWeight
  apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j))
  intro σ
  simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_right]

/-- Each ball sees exactly the empirical distribution of the fixed list.
Taking `x` to be an indicator gives the prescribed sector probabilities.
Taking `x` to be the sector energy gives preservation of the local mean energy. -/
theorem permutation_average (x : I → ℝ) (i : I) :
    (∑ σ : Equiv.Perm I, permutationWeight σ * x (σ i)) =
      (∑ j, x j) / (Fintype.card I : ℝ) := by
  have hsum :
      (∑ j, ∑ σ : Equiv.Perm I, permutationWeight σ * x (σ j)) = ∑ j, x j := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Equiv.sum_comp]
    rw [← Finset.sum_mul, permutationWeight_normalized, one_mul]
  have hconstant :
      (∑ j, ∑ σ : Equiv.Perm I, permutationWeight σ * x (σ j)) =
      (Fintype.card I : ℝ) *
        (∑ σ : Equiv.Perm I, permutationWeight σ * x (σ i)) := by
    calc
      _ = ∑ _j : I, ∑ σ : Equiv.Perm I, permutationWeight σ * x (σ i) := by
        apply Finset.sum_congr rfl
        intro j _
        exact permutation_average_position x j i
      _ = _ := by simp
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    have hnat : Fintype.card I ≠ 0 :=
      Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩)
    exact_mod_cast hnat
  apply (eq_div_iff hcard).2
  rw [← hsum, hconstant]
  ring

omit [DecidableEq I] in
theorem permutationCharge_neutral (q : I → ℝ) (hq : ∑ i, q i = 0)
    (σ : Equiv.Perm I) : ∑ i, permutationCharge q σ i = 0 := by
  unfold permutationCharge
  rw [Equiv.sum_comp, hq]

/-- Reindexing the uniform permutation average with a swap proves exchangeability
for two distinct positions without assuming it as a property of the moments. -/
theorem permutation_moment_exchangeable (q : I → ℝ) (i j k : I)
    (hji : j ≠ i) (hki : k ≠ i) :
    moment permutationWeight (permutationCharge q) i j =
      moment permutationWeight (permutationCharge q) i k := by
  unfold moment permutationWeight permutationCharge
  apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap j k))
  intro σ
  simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) (Ne.symm hki),
    Equiv.swap_apply_right]

/-- Exact covariance formula for the actual uniform permutation law. -/
theorem permutation_covariance (q : I → ℝ) (hq : ∑ i, q i = 0)
    (hcard : 1 < Fintype.card I) (i j : I) (hji : j ≠ i) :
    moment permutationWeight (permutationCharge q) i j =
      -moment permutationWeight (permutationCharge q) i i /
        ((Fintype.card I : ℝ) - 1) := by
  apply exchangeable_covariance permutationWeight (permutationCharge q)
    (permutationCharge_neutral q hq) hcard i _ _ rfl
  intro k hki
  exact permutation_moment_exchangeable q i k j hki hji

/-- The diagonal moment is exactly the empirical variance of the neutral list. -/
theorem permutation_variance (q : I → ℝ) (i : I) :
    moment permutationWeight (permutationCharge q) i i =
      (∑ j, q j * q j) / (Fintype.card I : ℝ) := by
  simpa only [moment, permutationCharge] using
    permutation_average (fun j => q j * q j) i

/-- Uniformly assigning a fixed neutral charge list gives nonpositive pair moments. -/
theorem permutation_covariance_nonpositive (q : I → ℝ) (hq : ∑ i, q i = 0)
    (hcard : 1 < Fintype.card I) (i j : I) (hji : j ≠ i) :
    moment permutationWeight (permutationCharge q) i j ≤ 0 := by
  apply exchangeable_covariance_nonpositive permutationWeight (permutationCharge q)
    permutationWeight_nonnegative (permutationCharge_neutral q hq) hcard i _ _ rfl
  intro k hki
  exact permutation_moment_exchangeable q i k j hki hji

/-- The averaged weighted cross interaction for these actual assignments is
nonpositive. It can be combined directly with the physical product-state identity. -/
theorem permutation_cross_interaction_nonpositive
    (q : I → ℝ) (hq : ∑ i, q i = 0) (hcard : 1 < Fintype.card I)
    (pairs : Finset (I × I)) (w : I × I → ℝ)
    (hdistinct : ∀ ij ∈ pairs, ij.2 ≠ ij.1)
    (hw : ∀ ij ∈ pairs, 0 ≤ w ij) :
    (∑ σ : Equiv.Perm I, permutationWeight σ *
      ∑ ij ∈ pairs, w ij *
        (permutationCharge q σ ij.1 * permutationCharge q σ ij.2)) ≤ 0 := by
  rw [average_cross_interaction]
  apply cross_interaction_nonpositive permutationWeight (permutationCharge q) pairs w hw
  intro ij hij
  exact permutation_covariance_nonpositive q hq hcard ij.1 ij.2 (hdistinct ij hij)

end PermutationAssignments

end Jellium.Canonical
