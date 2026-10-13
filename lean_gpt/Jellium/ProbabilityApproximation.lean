import Jellium.Canonical
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin

/-! Probability approximation used before the fixed-multiplicity construction. -/

open Filter Topology
open scoped BigOperators

namespace Jellium.ProbabilityApproximation

section Finite

variable {I : Type*} [Fintype I] [DecidableEq I]

def nonpivots (a b : I) : Finset I := (Finset.univ.erase a).erase b

theorem sum_split_two {R : Type*} [AddCommMonoid R] (f : I → R) (a b : I)
    (hab : a ≠ b) :
    (∑ i, f i) = f a + f b + ∑ i ∈ nonpivots a b, f i := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)]
  rw [← Finset.add_sum_erase (Finset.univ.erase a) f
    (show b ∈ Finset.univ.erase a by simp [Ne.symm hab])]
  simp only [nonpivots, add_assoc]

def pivotVector {R : Type*} (a b : I) (qa qb : R) (rest : I → R) (i : I) : R :=
  if i = a then qa else if i = b then qb else rest i

theorem pivotVector_sum {R : Type*} [AddCommMonoid R]
    (a b : I) (hab : a ≠ b) (qa qb : R) (rest : I → R) :
    (∑ i, pivotVector a b qa qb rest i) =
      qa + qb + ∑ i ∈ nonpivots a b, rest i := by
  rw [sum_split_two _ a b hab]
  simp only [pivotVector, ite_eq_right (Ne.symm hab)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hib : i ≠ b := (Finset.mem_erase.mp hi).1
  simp [hia, hib]

theorem pivotVector_weighted_sum {R : Type*} [CommSemiring R]
    (a b : I) (hab : a ≠ b) (qa qb : R) (rest w : I → R) :
    (∑ i, w i * pivotVector a b qa qb rest i) =
      w a * qa + w b * qb + ∑ i ∈ nonpivots a b, w i * rest i := by
  rw [sum_split_two _ a b hab]
  simp only [pivotVector, ite_eq_right (Ne.symm hab)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hib : i ≠ b := (Finset.mem_erase.mp hi).1
  simp [hia, hib]

/-- Reconstruction of two rational pivots enforces normalization and the
integer mean exactly, for arbitrary rational values at the other indices. -/
theorem rational_reconstruction_constraints (charge : I → ℕ) (n : ℕ)
    (a b : I) (hab : charge a ≠ charge b) (rest : I → ℚ) :
    let m := ∑ i ∈ nonpivots a b, rest i
    let z := ∑ i ∈ nonpivots a b, (charge i : ℚ) * rest i
    let qb := ((n : ℚ) - charge a - (z - charge a * m)) / (charge b - charge a)
    let qa := 1 - qb - m
    let q := pivotVector a b qa qb rest
    (∑ i, q i) = 1 ∧ (∑ i, (charge i : ℚ) * q i) = n := by
  dsimp only
  have hab' : a ≠ b := fun h => hab (congrArg charge h)
  rw [pivotVector_sum a b hab', pivotVector_weighted_sum a b hab']
  have hrat : (charge a : ℚ) ≠ charge b := by exact_mod_cast hab
  exact Canonical.rational_pivot_constraints (charge a) (charge b) n _ _ hrat

def reconstruct (charge : I → ℕ) (n : ℕ) (a b : I) (rest : I → ℚ) : I → ℚ :=
  let m := ∑ i ∈ nonpivots a b, rest i
  let z := ∑ i ∈ nonpivots a b, (charge i : ℚ) * rest i
  let qb := ((n : ℚ) - charge a - (z - charge a * m)) / (charge b - charge a)
  pivotVector a b (1 - qb - m) qb rest

theorem reconstruct_constraints (charge : I → ℕ) (n : ℕ)
    (a b : I) (hab : charge a ≠ charge b) (rest : I → ℚ) :
    (∑ i, reconstruct charge n a b rest i) = 1 ∧
      (∑ i, (charge i : ℚ) * reconstruct charge n a b rest i) = n :=
  rational_reconstruction_constraints charge n a b hab rest

theorem real_pivot_reconstruction (charge : I → ℕ) (n : ℕ)
    (a b : I) (hab : charge a ≠ charge b) (p : I → ℝ)
    (hmass : ∑ i, p i = 1) (hmean : ∑ i, (charge i : ℝ) * p i = n) :
    let m := ∑ i ∈ nonpivots a b, p i
    let z := ∑ i ∈ nonpivots a b, (charge i : ℝ) * p i
    let qb := ((n : ℝ) - charge a - (z - charge a * m)) / (charge b - charge a)
    qb = p b ∧ 1 - qb - m = p a := by
  dsimp only
  have hab' : a ≠ b := fun h => hab (congrArg charge h)
  have hm := sum_split_two p a b hab'
  have hz := sum_split_two (fun i => (charge i : ℝ) * p i) a b hab'
  rw [hmass] at hm
  rw [hmean] at hz
  have hden : (charge b : ℝ) - charge a ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast Ne.symm hab
  have hb : ((n : ℝ) - charge a -
      ((∑ i ∈ nonpivots a b, (charge i : ℝ) * p i) -
        charge a * ∑ i ∈ nonpivots a b, p i)) / (charge b - charge a) = p b := by
    apply (div_eq_iff hden).2
    nlinarith
  exact ⟨hb, by rw [hb]; linarith⟩

/-- Reconstructed rational vectors converge to the original constrained vector. -/
theorem reconstruct_tendsto (charge : I → ℕ) (n : ℕ)
    (a b : I) (hab : charge a ≠ charge b) (p : I → ℝ)
    (hmass : ∑ i, p i = 1) (hmean : ∑ i, (charge i : ℝ) * p i = n)
    (u : ℕ → I → ℚ)
    (hu : ∀ i, Tendsto (fun t => (u t i : ℝ)) atTop (𝓝 (p i))) :
    ∀ i, Tendsto (fun t => (reconstruct charge n a b (u t) i : ℝ)) atTop (𝓝 (p i)) := by
  have hab' : a ≠ b := fun h => hab (congrArg charge h)
  have hm := tendsto_finsetSum (nonpivots a b) (fun i _ => hu i)
  have hz := tendsto_finsetSum (nonpivots a b)
    (fun i _ => (hu i).const_mul (charge i : ℝ))
  obtain ⟨hlb, hla⟩ := Canonical.reconstructed_pivots_tendsto
    (charge a) (charge b) n _ _ _ _ hm hz
  obtain ⟨hb, ha⟩ := real_pivot_reconstruction charge n a b hab p hmass hmean
  rw [hb] at hlb
  rw [ha] at hla
  intro i
  by_cases hia : i = a
  · subst i
    simpa [reconstruct, pivotVector] using hla
  by_cases hib : i = b
  · subst i
    simpa [reconstruct, pivotVector, Ne.symm hab'] using hlb
  · simpa [reconstruct, pivotVector, hia, hib] using hu i

/-- Every finite probability vector with two positive pivots of different charge
admits arbitrarily close rational probability vectors with exactly the same
integer mean. The error is measured against any prescribed list of energies. -/
theorem finite_rational_mean_approximation (charge : I → ℕ) (n : ℕ)
    (a b : I) (hab : charge a ≠ charge b) (p energy : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpa : 0 < p a) (hpb : 0 < p b)
    (hmass : ∑ i, p i = 1) (hmean : ∑ i, (charge i : ℝ) * p i = n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1 ∧
      (∑ i, (charge i : ℚ) * q i) = n ∧
      |(∑ i, (q i : ℝ) * energy i) - ∑ i, p i * energy i| < ε := by
  classical
  choose u hmono hgt hlim using
    (fun i : I => Real.exists_seq_rat_strictAnti_tendsto (p i))
  let q : ℕ → I → ℚ := fun t => reconstruct charge n a b (fun i => u i t)
  have hq := reconstruct_tendsto charge n a b hab p hmass hmean
    (fun t i => u i t) hlim
  have hnonneg : ∀ᶠ t in atTop, ∀ i, 0 ≤ (q t i : ℝ) := by
    apply eventually_all.mpr
    intro i
    by_cases hia : i = a
    · subst i
      exact (Filter.Tendsto.eventually_const_lt hpa (hq a)).mono (fun _ h => le_of_lt h)
    by_cases hib : i = b
    · subst i
      exact (Filter.Tendsto.eventually_const_lt hpb (hq b)).mono (fun _ h => le_of_lt h)
    · apply Eventually.of_forall
      intro t
      have ht := le_trans (hp i) (le_of_lt (hgt i t))
      simpa [q, reconstruct, pivotVector, hia, hib] using ht
  have henergy : Tendsto (fun t => ∑ i, (q t i : ℝ) * energy i)
      atTop (𝓝 (∑ i, p i * energy i)) :=
    tendsto_finsetSum Finset.univ (fun i _ => (hq i).mul_const (energy i))
  have herr : Tendsto
      (fun t => |(∑ i, (q t i : ℝ) * energy i) - ∑ i, p i * energy i|)
      atTop (𝓝 0) := by
    simpa using (henergy.sub_const (∑ i, p i * energy i)).abs
  obtain ⟨t, ht, hterr⟩ :=
    (hnonneg.and (Filter.Tendsto.eventually_lt_const hε herr)).exists
  refine ⟨q t, ?_, ?_, ?_, hterr⟩
  · intro i
    exact_mod_cast ht i
  · exact (reconstruct_constraints charge n a b hab (fun i => u i t)).1
  · exact (reconstruct_constraints charge n a b hab (fun i => u i t)).2

end Finite

def addPivotCorrections (p : ℕ → ℝ) (a b : ℕ) (da db : ℝ) (k : ℕ) : ℝ :=
  p k + (if k = a then da else 0) + (if k = b then db else 0)

theorem corrected_weighted_sum (s : Finset ℕ) (p w : ℕ → ℝ)
    (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (da db : ℝ) :
    (∑ k ∈ s, addPivotCorrections p a b da db k * w k) =
      (∑ k ∈ s, p k * w k) + da * w a + db * w b := by
  simp only [addPivotCorrections, add_mul, Finset.sum_add_distrib]
  simp [ite_mul, ha, hb]

theorem corrected_sum (s : Finset ℕ) (p : ℕ → ℝ)
    (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (da db : ℝ) :
    (∑ k ∈ s, addPivotCorrections p a b da db k) =
      (∑ k ∈ s, p k) + da + db := by
  simpa using corrected_weighted_sum s p (fun _ => 1) a b ha hb da db

theorem corrected_nonnegative (p : ℕ → ℝ) (a b : ℕ) (hab : a ≠ b)
    (da db : ℝ) (hp : ∀ k, 0 ≤ p k)
    (ha : 0 < p a + da) (hb : 0 < p b + db) :
    ∀ k, 0 ≤ addPivotCorrections p a b da db k := by
  intro k
  by_cases hka : k = a
  · subst k
    simpa [addPivotCorrections, hab] using le_of_lt ha
  by_cases hkb : k = b
  · subst k
    simpa [addPivotCorrections, Ne.symm hab] using le_of_lt hb
  · simpa [addPivotCorrections, hka, hkb] using hp k

/-- A summable infinite law can be truncated while retaining its total mass,
integer mean, and energy expectation up to any requested error. The output is
a genuine finite rational probability vector. -/
theorem infinite_rational_mean_approximation_with_pivots
    (p energy : ℕ → ℝ) (n a b : ℕ) (hab : a ≠ b)
    (hp : ∀ k, 0 ≤ p k) (hpa : 0 < p a) (hpb : 0 < p b)
    (hpsum : Summable p) (hmeanSum : Summable (fun k : ℕ => (k : ℝ) * p k))
    (henergySum : Summable (fun k => p k * energy k))
    (hmass : ∑' k, p k = 1) (hmean : ∑' k : ℕ, (k : ℝ) * p k = n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∃ q : Fin K → ℚ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1 ∧
      (∑ i, (i.val : ℚ) * q i) = n ∧
      |(∑ i : Fin K, (q i : ℝ) * energy i.val) - ∑' k, p k * energy k| < ε := by
  classical
  let t : ℕ → ℝ := fun K => 1 - ∑ k ∈ Finset.range K, p k
  let s : ℕ → ℝ := fun K => (n : ℝ) - ∑ k ∈ Finset.range K, (k : ℝ) * p k
  let da : ℕ → ℝ := fun K => ((b : ℝ) * t K - s K) / (b - a)
  let db : ℕ → ℝ := fun K => (s K - (a : ℝ) * t K) / (b - a)
  let corrected : ℕ → ℕ → ℝ := fun K => addPivotCorrections p a b (da K) (db K)
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa [t, hmass] using hpsum.tendsto_sum_tsum_nat.const_sub 1
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa [s, hmean] using hmeanSum.tendsto_sum_tsum_nat.const_sub (n : ℝ)
  obtain ⟨hda, hdb⟩ := Canonical.tail_corrections_tendsto_zero (a : ℝ) b t s ht hs
  have hpos := Canonical.tail_corrected_weights_eventually_positive
    (a : ℝ) b (p a) (p b) t s hpa hpb ht hs
  have he : Tendsto (fun K => (∑ k ∈ Finset.range K, p k * energy k) +
      da K * energy a + db K * energy b)
      atTop (𝓝 (∑' k, p k * energy k)) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      (henergySum.tendsto_sum_tsum_nat.add (hda.mul_const (energy a))).add
        (hdb.mul_const (energy b))
  have herr : ∀ᶠ K in atTop,
      |((∑ k ∈ Finset.range K, p k * energy k) + da K * energy a + db K * energy b) -
        ∑' k, p k * energy k| < ε / 2 := by
    have hlim : Tendsto (fun K =>
        |((∑ k ∈ Finset.range K, p k * energy k) + da K * energy a + db K * energy b) -
          ∑' k, p k * energy k|) atTop (𝓝 0) := by
      simpa using (he.sub_const (∑' k, p k * energy k)).abs
    exact Filter.Tendsto.eventually_lt_const (by linarith : 0 < ε / 2) hlim
  obtain ⟨K, hK, hposK, herrK⟩ :=
    ((eventually_gt_atTop (max a b)).and (hpos.and herr)).exists
  have haK : a < K := lt_of_le_of_lt (le_max_left a b) hK
  have hbK : b < K := lt_of_le_of_lt (le_max_right a b) hK
  let ia : Fin K := ⟨a, haK⟩
  let ib : Fin K := ⟨b, hbK⟩
  have habreal : (a : ℝ) ≠ b := by exact_mod_cast hab
  have hc := Canonical.corrected_constraints (a : ℝ) b (t K) (s K)
    (∑ k ∈ Finset.range K, p k) (∑ k ∈ Finset.range K, (k : ℝ) * p k) n
    habreal (by dsimp [t]; ring) (by dsimp [s]; ring)
  have hcmass : ∑ i : Fin K, corrected K i.val = 1 := by
    rw [← Finset.sum_range]
    rw [corrected_sum _ p a b (Finset.mem_range.mpr haK) (Finset.mem_range.mpr hbK)]
    exact hc.1
  have hcmean : ∑ i : Fin K, (i.val : ℝ) * corrected K i.val = n := by
    rw [← Finset.sum_range (fun k : ℕ => (k : ℝ) * corrected K k)]
    have hw := corrected_weighted_sum (Finset.range K) p (fun k => (k : ℝ)) a b
      (Finset.mem_range.mpr haK) (Finset.mem_range.mpr hbK) (da K) (db K)
    have heq : (∑ k ∈ Finset.range K, (k : ℝ) * corrected K k) =
        (∑ k ∈ Finset.range K, (k : ℝ) * p k) + (a : ℝ) * da K + (b : ℝ) * db K := by
      simpa only [mul_comm] using hw
    rw [heq]
    exact hc.2
  have hcnonneg : ∀ i : Fin K, 0 ≤ corrected K i.val :=
    fun i => corrected_nonnegative p a b hab (da K) (db K) hp hposK.1 hposK.2 i.val
  have hcpa : 0 < corrected K ia.val := by
    simpa [corrected, addPivotCorrections, ia, hab] using hposK.1
  have hcpb : 0 < corrected K ib.val := by
    simpa [corrected, addPivotCorrections, ib, Ne.symm hab] using hposK.2
  obtain ⟨q, hqpos, hqmass, hqmean, hqenergy⟩ :=
    finite_rational_mean_approximation (fun i : Fin K => i.val) n ia ib hab
      (fun i => corrected K i.val) (fun i => energy i.val)
      hcnonneg hcpa hcpb hcmass hcmean (ε / 2) (by linarith)
  refine ⟨K, q, hqpos, hqmass, hqmean, ?_⟩
  have hcorrectedEnergy :
      (∑ i : Fin K, corrected K i.val * energy i.val) =
        (∑ k ∈ Finset.range K, p k * energy k) + da K * energy a + db K * energy b := by
    rw [← Finset.sum_range (fun k : ℕ => corrected K k * energy k)]
    exact corrected_weighted_sum _ p energy a b
      (Finset.mem_range.mpr haK) (Finset.mem_range.mpr hbK) (da K) (db K)
  rw [← hcorrectedEnergy] at herrK
  have htriangle := abs_add_le
    ((∑ i : Fin K, (q i : ℝ) * energy i.val) - ∑ i : Fin K, corrected K i.val * energy i.val)
    ((∑ i : Fin K, corrected K i.val * energy i.val) - ∑' k, p k * energy k)
  have hid : ((∑ i : Fin K, (q i : ℝ) * energy i.val) - ∑ i : Fin K, corrected K i.val * energy i.val) +
      ((∑ i : Fin K, corrected K i.val * energy i.val) - ∑' k, p k * energy k) =
      (∑ i : Fin K, (q i : ℝ) * energy i.val) - ∑' k, p k * energy k := by ring
  rw [hid] at htriangle
  linarith

/-- A normalized law with integer mean is either concentrated at that integer
or has two distinct occupied sectors. No unproved sector-selection principle is used. -/
theorem point_mass_or_two_pivots (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ k, 0 ≤ p k) (hmass : ∑' k, p k = 1)
    (hmean : ∑' k : ℕ, (k : ℝ) * p k = n) :
    p n = 1 ∨ ∃ a b : ℕ, a ≠ b ∧ 0 < p a ∧ 0 < p b := by
  classical
  by_cases hpn : p n = 1
  · exact Or.inl hpn
  · right
    have hsome : ∃ a, 0 < p a := by
      by_contra h
      push Not at h
      have hz : ∀ k, p k = 0 := fun k => le_antisymm (h k) (hp k)
      simp [hz] at hmass
    obtain ⟨a, ha⟩ := hsome
    by_contra htwo
    have hz : ∀ k, k ≠ a → p k = 0 := by
      intro k hka
      apply le_antisymm _ (hp k)
      by_contra hpos
      have hk : 0 < p k := lt_of_not_ge hpos
      exact htwo ⟨a, k, Ne.symm hka, ha, hk⟩
    have hpa : p a = 1 := by
      rw [tsum_eq_single a hz] at hmass
      exact hmass
    have hmeanA : (a : ℝ) * p a = n := by
      rw [tsum_eq_single a (fun k hk => by simp [hz k hk])] at hmean
      exact hmean
    rw [hpa, mul_one] at hmeanA
    have han : a = n := by exact_mod_cast hmeanA
    exact hpn (han ▸ hpa)

theorem point_mass_off_support (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (hmass : ∑' k, p k = 1) (hpn : p n = 1) :
    ∀ k, k ≠ n → p k = 0 := by
  intro k hkn
  have hbound := Summable.sum_le_tsum ({n, k} : Finset ℕ) (fun j _ => hp j) hsum
  rw [Finset.sum_pair (Ne.symm hkn), hmass, hpn] at hbound
  exact le_antisymm (by linarith) (hp k)

/-- The complete rational approximation theorem, including the point-mass case. -/
theorem infinite_rational_mean_approximation
    (p energy : ℕ → ℝ) (n : ℕ)
    (hp : ∀ k, 0 ≤ p k)
    (hpsum : Summable p) (hmeanSum : Summable (fun k : ℕ => (k : ℝ) * p k))
    (henergySum : Summable (fun k => p k * energy k))
    (hmass : ∑' k, p k = 1) (hmean : ∑' k : ℕ, (k : ℝ) * p k = n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∃ q : Fin K → ℚ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1 ∧
      (∑ i, (i.val : ℚ) * q i) = n ∧
      |(∑ i : Fin K, (q i : ℝ) * energy i.val) - ∑' k, p k * energy k| < ε := by
  classical
  rcases point_mass_or_two_pivots p n hp hmass hmean with hpn | ⟨a, b, hab, ha, hb⟩
  · let i₀ : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let q : Fin (n + 1) → ℚ := fun i => if i = i₀ then 1 else 0
    have hoff := point_mass_off_support p n hp hpsum hmass hpn
    have he : (∑' k, p k * energy k) = energy n := by
      rw [tsum_eq_single n (fun k hk => by simp [hoff k hk]), hpn, one_mul]
    refine ⟨n + 1, q, ?_, ?_, ?_, ?_⟩
    · intro i
      simp only [q]
      split_ifs <;> norm_num
    · simp [q]
    · simp [q, mul_ite, i₀]
    · simpa [q, apply_ite, ite_mul, i₀, he] using hε
  · exact infinite_rational_mean_approximation_with_pivots p energy n a b hab hp ha hb
      hpsum hmeanSum henergySum hmass hmean ε hε

section Multiplicities

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Rational probabilities are realized by exact integer multiplicities, with
the total number chosen as a cube so it fits the lattice-ball construction. -/
theorem exists_cubic_multiplicities (q : I → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = 1) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ count : I → ℕ,
      (∑ i, count i) = m ^ 3 ∧ ∀ i, (count i : ℚ) = (m ^ 3 : ℕ) * q i := by
  classical
  let D : ℕ := ∏ i, (q i).den
  let m : ℕ := 2 * D
  have hD : 0 < D := Finset.prod_pos (fun i _ => (q i).den_pos)
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hex : ∀ i, ∃ c : ℕ, (c : ℚ) = (m ^ 3 : ℕ) * q i := by
    intro i
    have hdivD : (q i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hdivm : (q i).den ∣ m := by
      apply dvd_trans hdivD
      refine ⟨2, ?_⟩
      dsimp [m]
      ring
    have hdiv : (q i).den ∣ m ^ 3 := hdivm.pow (by decide : (3 : ℕ) ≠ 0)
    obtain ⟨d, hd⟩ := hdiv
    refine ⟨d * (q i).num.toNat, ?_⟩
    have hn : 0 ≤ (q i).num := Rat.num_nonneg.mpr (hq i)
    have hnat : ((q i).num.toNat : ℚ) = ((q i).num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
    have hden : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
    have hid : ((q i).num : ℚ) = q i * (q i).den :=
      (div_eq_iff hden).mp (q i).num_div_den
    rw [Nat.cast_mul, hnat, hid, hd, Nat.cast_mul]
    ring
  choose count hc using hex
  have hsum : (∑ i, (count i : ℚ)) = (m ^ 3 : ℕ) := by
    simp_rw [hc]
    rw [← Finset.mul_sum, hmass, mul_one]
  exact ⟨m, hm, count, by exact_mod_cast hsum, hc⟩

/-- A dependent pair enumerates each sector precisely `count i` times. -/
def RepeatedIndex (count : I → ℕ) := Σ i : I, Fin (count i)

instance repeatedIndexFintype (count : I → ℕ) : Fintype (RepeatedIndex count) :=
  inferInstanceAs (Fintype (Σ i : I, Fin (count i)))

instance repeatedIndexDecidableEq (count : I → ℕ) : DecidableEq (RepeatedIndex count) :=
  inferInstanceAs (DecidableEq (Σ i : I, Fin (count i)))

omit [DecidableEq I] in
theorem repeatedIndex_card (count : I → ℕ) :
    Fintype.card (RepeatedIndex count) = ∑ i, count i := by
  change Fintype.card (Σ i : I, Fin (count i)) = _
  rw [Fintype.card_sigma]
  simp

omit [DecidableEq I] in
theorem sum_repeated_real (count : I → ℕ) (value : I → ℝ) :
    (∑ j : RepeatedIndex count, value j.1) = ∑ i, (count i : ℝ) * value i := by
  change (∑ j : (Σ i : I, Fin (count i)), value j.1) = _
  rw [Fintype.sum_sigma]
  simp

omit [DecidableEq I] in
theorem sum_repeated_nat (count : I → ℕ) (value : I → ℕ) :
    (∑ j : RepeatedIndex count, value j.1) = ∑ i, count i * value i := by
  change (∑ j : (Σ i : I, Fin (count i)), value j.1) = _
  rw [Fintype.sum_sigma]
  simp

omit [DecidableEq I] in
/-- The exact mean and energy identities needed by the ball-state construction. -/
theorem repeated_list_mean_and_energy (q : I → ℚ) (count charge : I → ℕ)
    (M n : ℕ) (energy : I → ℝ)
    (hc : ∀ i, (count i : ℚ) = (M : ℚ) * q i)
    (hmean : ∑ i, (charge i : ℚ) * q i = n) :
    (∑ j : RepeatedIndex count, charge j.1) = M * n ∧
      (∑ j : RepeatedIndex count, energy j.1) =
        (M : ℝ) * ∑ i, (q i : ℝ) * energy i := by
  constructor
  · rw [sum_repeated_nat]
    have hsum : (∑ i, (count i : ℚ) * (charge i : ℚ)) = (M : ℚ) * n := by
      simp_rw [hc]
      calc
        _ = (M : ℚ) * ∑ i, (charge i : ℚ) * q i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hmean]
    exact_mod_cast hsum
  · rw [sum_repeated_real, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (count i : ℝ) = (M : ℝ) * (q i : ℝ) := by exact_mod_cast hc i
    rw [hi]
    ring

end Multiplicities

/-- End-to-end approximation by a fixed list of integer sectors. The number
of list entries is a cube, the total particle number is exact, and its average
energy approximates the original infinite-sector expectation. -/
theorem exists_cubic_sector_list
    (p energy : ℕ → ℝ) (n : ℕ)
    (hp : ∀ k, 0 ≤ p k)
    (hpsum : Summable p) (hmeanSum : Summable (fun k : ℕ => (k : ℝ) * p k))
    (henergySum : Summable (fun k => p k * energy k))
    (hmass : ∑' k, p k = 1) (hmean : ∑' k : ℕ, (k : ℝ) * p k = n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m K : ℕ, 2 ≤ m ∧ ∃ count : Fin K → ℕ,
      Fintype.card (RepeatedIndex count) = m ^ 3 ∧
      (∑ j : RepeatedIndex count, j.1.val) = m ^ 3 * n ∧
      |(∑ j : RepeatedIndex count, energy j.1.val) / (m ^ 3 : ℕ) -
        ∑' k, p k * energy k| < ε := by
  obtain ⟨K, q, hqpos, hqmass, hqmean, hqenergy⟩ :=
    infinite_rational_mean_approximation p energy n hp hpsum hmeanSum henergySum
      hmass hmean ε hε
  obtain ⟨m, hm, count, hcountsum, hcount⟩ := exists_cubic_multiplicities q hqpos hqmass
  obtain ⟨hcmean, hcenergy⟩ := repeated_list_mean_and_energy q count
    (fun i : Fin K => i.val) (m ^ 3) n (fun i => energy i.val) hcount hqmean
  refine ⟨m, K, hm, count, ?_, hcmean, ?_⟩
  · rw [repeatedIndex_card, hcountsum]
  · rw [hcenergy]
    have hm0 : ((m ^ 3 : ℕ) : ℝ) ≠ 0 := by
      have : m ≠ 0 := by omega
      exact_mod_cast pow_ne_zero 3 this
    rw [mul_div_cancel_left₀ _ hm0]
    exact hqenergy

end Jellium.ProbabilityApproximation
