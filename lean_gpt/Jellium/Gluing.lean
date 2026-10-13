import Jellium.Electrostatics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic.Linarith

/-!
The actual square-root gluing used for the fluid. Disjoint modified regions
let one add compactly supported corrections to the square root of the outer
background. This supplies Sobolev membership by addition, without assuming
Sobolev regularity of the newly constructed fluid.
-/

open Set Finset

namespace Jellium.Gluing

variable {X I : Type*}

noncomputable def gluedRoot (s : Finset I) (base : X → ℝ) (b : ℝ)
    (profile : I → X → ℝ) (x : X) : ℝ :=
  base x + ∑ i ∈ s, b * (profile i x - 1)

noncomputable def gluedDensity (s : Finset I) (base : X → ℝ) (b : ℝ)
    (profile : I → X → ℝ) (x : X) : ℝ :=
  base x ^ 2 + ∑ i ∈ s, b ^ 2 * (profile i x ^ 2 - 1)

theorem glued_root_properties
    (s : Finset I) (region : I → Set X) (base : X → ℝ) (b : ℝ)
    (profile : I → X → ℝ)
    (hdisjoint : (s : Set I).Pairwise (fun i j => Disjoint (region i) (region j)))
    (hbase : ∀ x, 0 ≤ base x) (hb : 0 ≤ b)
    (hprofile : ∀ i ∈ s, ∀ x, 0 ≤ profile i x)
    (houtside : ∀ i ∈ s, ∀ x, x ∉ region i → profile i x = 1)
    (hplateau : ∀ i ∈ s, ∀ x ∈ region i, base x = b)
    (x : X) :
    0 ≤ gluedRoot s base b profile x ∧
      gluedDensity s base b profile x = gluedRoot s base b profile x ^ 2 := by
  classical
  by_cases hactive : ∃ i ∈ s, x ∈ region i
  · obtain ⟨j, hj, hxj⟩ := hactive
    have hother (i : I) (hi : i ∈ s) (hij : i ≠ j) : profile i x = 1 := by
      apply houtside i hi x
      intro hxi
      exact Set.disjoint_left.1 (hdisjoint hi hj hij) hxi hxj
    have hroot : (∑ i ∈ s, b * (profile i x - 1)) = b * (profile j x - 1) := by
      apply Finset.sum_eq_single j
      · intro i hi hij
        rw [hother i hi hij]
        ring
      · exact fun h => (h hj).elim
    have hdensity : (∑ i ∈ s, b ^ 2 * (profile i x ^ 2 - 1)) =
        b ^ 2 * (profile j x ^ 2 - 1) := by
      apply Finset.sum_eq_single j
      · intro i hi hij
        rw [hother i hi hij]
        ring
      · exact fun h => (h hj).elim
    simp only [gluedRoot, gluedDensity, hroot, hdensity, hplateau j hj x hxj]
    constructor
    · nlinarith [mul_nonneg hb (hprofile j hj x)]
    · ring
  · have hzero (i : I) (hi : i ∈ s) : profile i x = 1 :=
      houtside i hi x (fun hx => hactive ⟨i, hi, hx⟩)
    have hroot : (∑ i ∈ s, b * (profile i x - 1)) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hzero i hi]; ring)
    have hdensity : (∑ i ∈ s, b ^ 2 * (profile i x ^ 2 - 1)) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hzero i hi]; ring)
    simpa [gluedRoot, gluedDensity, hroot, hdensity] using hbase x

theorem sqrt_gluedDensity
    (s : Finset I) (region : I → Set X) (base : X → ℝ) (b : ℝ)
    (profile : I → X → ℝ)
    (hdisjoint : (s : Set I).Pairwise (fun i j => Disjoint (region i) (region j)))
    (hbase : ∀ x, 0 ≤ base x) (hb : 0 ≤ b)
    (hprofile : ∀ i ∈ s, ∀ x, 0 ≤ profile i x)
    (houtside : ∀ i ∈ s, ∀ x, x ∉ region i → profile i x = 1)
    (hplateau : ∀ i ∈ s, ∀ x ∈ region i, base x = b) :
    (fun x => Real.sqrt (gluedDensity s base b profile x)) = gluedRoot s base b profile := by
  funext x
  obtain ⟨hnonneg, hsquare⟩ :=
    glued_root_properties s region base b profile hdisjoint hbase hb hprofile houtside hplateau x
  rw [hsquare, Real.sqrt_sq hnonneg]

/-- Sobolev membership follows from the actual square-root formula. The
submodule can be the standard H¹ submodule. Only membership of the background
root and the smooth compactly supported local corrections is required. -/
theorem sqrt_gluedDensity_mem
    (H1 : Submodule ℝ (X → ℝ))
    (s : Finset I) (region : I → Set X) (base : X → ℝ) (b : ℝ)
    (profile : I → X → ℝ)
    (hdisjoint : (s : Set I).Pairwise (fun i j => Disjoint (region i) (region j)))
    (hbase : ∀ x, 0 ≤ base x) (hb : 0 ≤ b)
    (hprofile : ∀ i ∈ s, ∀ x, 0 ≤ profile i x)
    (houtside : ∀ i ∈ s, ∀ x, x ∉ region i → profile i x = 1)
    (hplateau : ∀ i ∈ s, ∀ x ∈ region i, base x = b)
    (hbase_mem : base ∈ H1)
    (hcorrection_mem : ∀ i ∈ s, (fun x => b * (profile i x - 1)) ∈ H1) :
    (fun x => Real.sqrt (gluedDensity s base b profile x)) ∈ H1 := by
  rw [sqrt_gluedDensity s region base b profile hdisjoint hbase hb hprofile houtside hplateau]
  have heq : gluedRoot s base b profile = base + ∑ i ∈ s, (fun x => b * (profile i x - 1)) := by
    funext x
    simp [gluedRoot]
  rw [heq]
  exact H1.add_mem hbase_mem (H1.sum_mem hcorrection_mem)

/-- Energy additivity for a background root and disjoint local corrections.
For the Dirichlet form, the zero mixed terms come from its standard locality
and the background plateau. This is the exact identity before estimating the
individual collar gradients. -/
theorem gradient_energy_identity
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (G : CoulombForm V) (s : Finset I) (base : V) (correction : I → V)
    (hbackground : ∀ i ∈ s, G.form base (correction i) = 0)
    (hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → G.form (correction i) (correction j) = 0) :
    G.form (base + ∑ i ∈ s, correction i) (base + ∑ i ∈ s, correction i) =
      G.form base base + ∑ i ∈ s, G.form (correction i) (correction i) := by
  have hzero : G.form base (∑ i ∈ s, correction i) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero hbackground
  have hzero' : G.form (∑ i ∈ s, correction i) base = 0 := by
    rw [G.symmetric]
    exact hzero
  simp only [map_add, LinearMap.add_apply]
  rw [hzero, hzero', G.self_sum s correction hdisjoint]
  ring

end Jellium.Gluing
