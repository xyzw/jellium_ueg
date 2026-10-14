import Jellium.Domains
import Mathlib.Data.Finset.Max

/-! Concrete nearest-neighbour balls for the local orbital construction.
The inserted length one also handles a configuration with a single particle. -/

open Set Metric
open scoped BigOperators

namespace Jellium.OrbitalGeometry

open Domains

variable {P : ℕ}

noncomputable def admissibleLengths (c : Fin P → Space) (i : Fin P) : Finset ℝ := by
  classical
  exact insert 1 ((Finset.univ.erase i).image (fun j => dist (c i) (c j)))

noncomputable def clearance (c : Fin P → Space) (i : Fin P) : ℝ :=
  (admissibleLengths c i).min' (by
    classical
    exact Finset.insert_nonempty _ _)

noncomputable def radius (c : Fin P → Space) (i : Fin P) : ℝ := clearance c i / 2

theorem clearance_mem (c : Fin P → Space) (i : Fin P) :
    clearance c i ∈ admissibleLengths c i := Finset.min'_mem _ _

theorem clearance_pos (c : Fin P → Space) (hc : Function.Injective c) (i : Fin P) :
    0 < clearance c i := by
  classical
  have hm := clearance_mem c i
  simp only [admissibleLengths, Finset.mem_insert, Finset.mem_image, Finset.mem_erase,
    Finset.mem_univ, and_true] at hm
  rcases hm with h | ⟨j, hji, h⟩
  · rw [h]
    norm_num
  · rw [← h]
    exact dist_pos.mpr (fun hij => hji (hc hij).symm)

theorem clearance_le_one (c : Fin P → Space) (i : Fin P) : clearance c i ≤ 1 := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem clearance_le_dist (c : Fin P → Space) (i j : Fin P) (hij : i ≠ j) :
    clearance c i ≤ dist (c i) (c j) := by
  classical
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩, rfl⟩

theorem radius_pos (c : Fin P → Space) (hc : Function.Injective c) (i : Fin P) :
    0 < radius c i := div_pos (clearance_pos c hc i) (by norm_num)

theorem radius_le_half (c : Fin P → Space) (i : Fin P) : radius c i ≤ 1 / 2 := by
  dsimp [radius]
  exact div_le_div_of_nonneg_right (clearance_le_one c i) (by norm_num)

theorem radius_le_half_dist (c : Fin P → Space) (i j : Fin P) (hij : i ≠ j) :
    radius c i ≤ dist (c i) (c j) / 2 := by
  dsimp [radius]
  exact div_le_div_of_nonneg_right (clearance_le_dist c i j hij) (by norm_num)

theorem balls_pairwise_disjoint (c : Fin P → Space) :
    Pairwise (fun i j => Disjoint (ball (c i) (radius c i)) (ball (c j) (radius c j))) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  have hi := radius_le_half_dist c i j hij
  have hj := radius_le_half_dist c j i hij.symm
  rw [dist_comm (c j) (c i)] at hj
  linarith

theorem ball_subset_annulus (c : Fin P → Space) (i : Fin P) (R S : ℝ)
    (hinner : R + 1 < ‖c i‖) (houter : ‖c i‖ < S - 1) :
    ball (c i) (radius c i) ⊆ {x : Space | R < ‖x‖ ∧ ‖x‖ < S} := by
  intro x hx
  have hd := mem_ball.mp hx
  have hr := radius_le_half c i
  have htri := dist_triangle x (c i) 0
  have htri' := dist_triangle (c i) x 0
  simp only [dist_zero_right] at htri htri'
  rw [dist_comm (c i) x] at htri'
  constructor <;> linarith

theorem closedBall_subset_annulus (c : Fin P → Space) (i : Fin P) (R S : ℝ)
    (hinner : R + 1 < ‖c i‖) (houter : ‖c i‖ < S - 1) :
    closedBall (c i) (radius c i) ⊆ {x : Space | R < ‖x‖ ∧ ‖x‖ < S} := by
  intro x hx
  have hd := mem_closedBall.mp hx
  have hr := radius_le_half c i
  have htri := dist_triangle x (c i) 0
  have htri' := dist_triangle (c i) x 0
  simp only [dist_zero_right] at htri htri'
  rw [dist_comm (c i) x] at htri'
  constructor <;> linarith

theorem radius_singleton (c : Fin 1 → Space) (i : Fin 1) : radius c i = 1 / 2 := by
  classical
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  norm_num [radius, clearance, admissibleLengths]

/-- The inverse-square pair cost before the factor `8 * pi^2`. -/
noncomputable def shortPair (c : Fin P → Space) (i j : Fin P) : ℝ :=
  if dist (c i) (c j) ≤ 1 then (dist (c i) (c j))⁻¹ ^ 2 else 0

theorem shortPair_nonneg (c : Fin P → Space) (i j : Fin P) : 0 ≤ shortPair c i j := by
  unfold shortPair
  split <;> positivity

theorem shortPair_symm (c : Fin P → Space) (i j : Fin P) :
    shortPair c i j = shortPair c j i := by simp only [shortPair, dist_comm]

/-- Half of the ordered pair sum is the unordered pair sum. -/
noncomputable def pairPenalty (c : Fin P → Space) : ℝ := by
  classical
  exact 4 * Real.pi ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, shortPair c i j

theorem pairPenalty_nonneg (c : Fin P → Space) : 0 ≤ pairPenalty c := by
  classical
  unfold pairPenalty
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => shortPair_nonneg c i j))

noncomputable def kineticSum (c : Fin P → Space) : ℝ :=
  ∑ i, (Real.pi / radius c i) ^ 2

theorem clearance_inv_sq_bound (c : Fin P → Space) (i : Fin P) :
    (clearance c i)⁻¹ ^ 2 ≤ 1 + ∑ j ∈ Finset.univ.erase i, shortPair c i j := by
  classical
  have hs : 0 ≤ ∑ j ∈ Finset.univ.erase i, shortPair c i j :=
    Finset.sum_nonneg (fun j _ => shortPair_nonneg c i j)
  have hm := clearance_mem c i
  simp only [admissibleLengths, Finset.mem_insert, Finset.mem_image, Finset.mem_erase,
    Finset.mem_univ, and_true] at hm
  rcases hm with h | ⟨j, hji, h⟩
  · calc
      (clearance c i)⁻¹ ^ 2 = 1 := by rw [h]; norm_num
      _ ≤ 1 + ∑ j ∈ Finset.univ.erase i, shortPair c i j := le_add_of_nonneg_right hs
  · have hd : dist (c i) (c j) ≤ 1 := h ▸ clearance_le_one c i
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    have hle := Finset.single_le_sum (fun k _ => shortPair_nonneg c i k) hmem
    rw [shortPair, ite_eq_left hd, h] at hle
    linarith

theorem kinetic_sum_bound (c : Fin P → Space) :
    kineticSum c ≤ pairPenalty c + 4 * Real.pi ^ 2 * P := by
  classical
  have hpoint : ∀ i, (Real.pi / radius c i) ^ 2 ≤
      4 * Real.pi ^ 2 * (1 + ∑ j ∈ Finset.univ.erase i, shortPair c i j) := by
    intro i
    have h := mul_le_mul_of_nonneg_left (clearance_inv_sq_bound c i)
      (by positivity : 0 ≤ 4 * Real.pi ^ 2)
    calc
      (Real.pi / radius c i) ^ 2 = 4 * Real.pi ^ 2 * (clearance c i)⁻¹ ^ 2 := by
        simp only [radius, div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
      _ ≤ _ := h
  calc
    kineticSum c ≤ ∑ i, 4 * Real.pi ^ 2 *
        (1 + ∑ j ∈ Finset.univ.erase i, shortPair c i j) := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = pairPenalty c + 4 * Real.pi ^ 2 * P := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, pairPenalty, ← Finset.mul_sum]
      ring

end Jellium.OrbitalGeometry
