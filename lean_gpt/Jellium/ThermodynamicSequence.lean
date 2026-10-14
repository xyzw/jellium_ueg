import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The scalar convergence lemma in Appendix A, `lem:LN_sequences`.

This supplements the main equality proof. The physical Lieb–Narnhofer limit
remains an explicit literature input. No packing or operator construction is
asserted here.
-/

open Filter Topology
open scoped BigOperators

namespace Jellium.ThermodynamicSequence

/-- The geometric upper envelope of the previous sequence values. -/
def envelope (a : ℕ → ℝ) (γ C : ℝ) (n : ℕ) : ℝ :=
  (1 - γ) * ∑ j ∈ Finset.range n, γ ^ (n - 1 - j) * a j + C * γ ^ n

theorem envelope_zero (a : ℕ → ℝ) (γ C : ℝ) : envelope a γ C 0 = C := by
  simp [envelope]

theorem envelope_succ (a : ℕ → ℝ) (γ C : ℝ) (n : ℕ) :
    envelope a γ C (n + 1) = γ * envelope a γ C n + (1 - γ) * a n := by
  have hsum : ∑ j ∈ Finset.range n, γ ^ (n - j) * a j =
      γ * ∑ j ∈ Finset.range n, γ ^ (n - 1 - j) * a j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have he : n - j = (n - 1 - j) + 1 := by omega
    rw [he, pow_succ]
    ring
  simp only [envelope, Finset.sum_range_succ, Nat.add_sub_cancel,
    Nat.sub_self, pow_zero, one_mul, pow_succ]
  rw [hsum]
  ring

theorem envelope_lower_bound (a : ℕ → ℝ) (γ C L : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (ha : ∀ n, L ≤ a n) (n : ℕ) :
    min C L ≤ envelope a γ C n := by
  induction n with
  | zero => simp [envelope_zero]
  | succ n ih =>
    rw [envelope_succ]
    have h₁ := mul_le_mul_of_nonneg_left ih hγ
    have h₂ := mul_le_mul_of_nonneg_left ((min_le_right C L).trans (ha n))
      (sub_nonneg.mpr hγ1)
    nlinarith only [h₁, h₂]

/-- A bounded-below sequence under the geometric recursion has a finite limit.
The error coefficient may be any real number, so in particular this covers
the manuscript's nonnegative coefficient. The recursion starts at index one.
-/
theorem exists_limit_of_geometric_recursion (a : ℕ → ℝ) (γ C : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hlower : ∃ L : ℝ, ∀ n, L ≤ a n)
    (hrec : ∀ n, 1 ≤ n →
      a n ≤ (1 - γ) * ∑ j ∈ Finset.range n, γ ^ (n - 1 - j) * a j + C * γ ^ n) :
    ∃ l : ℝ, Tendsto a atTop (𝓝 l) := by
  obtain ⟨L, hL⟩ := hlower
  let b := envelope a γ C
  have hstep (n : ℕ) (hn : 1 ≤ n) : b (n + 1) ≤ b n := by
    dsimp [b]
    rw [envelope_succ]
    have h := mul_le_mul_of_nonneg_left (hrec n hn) (sub_nonneg.mpr hγ1.le)
    change (1 - γ) * a n ≤ (1 - γ) * envelope a γ C n at h
    nlinarith only [h]
  have hanti : Antitone (fun n => b (n + 1)) := by
    apply antitone_nat_of_succ_le
    intro n
    exact hstep (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have hbounded : BddBelow (Set.range (fun n => b (n + 1))) := by
    refine ⟨min C L, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact envelope_lower_bound a γ C L hγ hγ1.le hL (n + 1)
  let l := ⨅ n, b (n + 1)
  have hshift : Tendsto (fun n => b (n + 1)) atTop (𝓝 l) :=
    tendsto_atTop_ciInf hanti hbounded
  have hb : Tendsto b atTop (𝓝 l) := (tendsto_add_atTop_iff_nat 1).mp hshift
  have hquot := (hshift.sub (hb.const_mul γ)).div_const (1 - γ)
  have hne : 1 - γ ≠ 0 := ne_of_gt (sub_pos.mpr hγ1)
  have hid (n : ℕ) : (b (n + 1) - γ * b n) / (1 - γ) = a n := by
    dsimp [b]
    rw [envelope_succ]
    field_simp
    ring
  have hlim : (l - γ * l) / (1 - γ) = l := by
    apply (div_eq_iff hne).2
    ring
  refine ⟨l, ?_⟩
  simpa only [hid, hlim] using hquot

end Jellium.ThermodynamicSequence
