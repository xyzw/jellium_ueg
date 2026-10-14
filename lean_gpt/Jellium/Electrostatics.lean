import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
The algebra of the Coulomb part of Section 6.

`CoulombForm` is an explicit interface for the standard positivity, symmetry
and bilinearity of finite Coulomb energy. It does not assert Newton's theorem,
the existence of any state, or the construction of a collar or a packing.
The spatial hypotheses needed to get zero cross interactions remain visible
as hypotheses of the theorems below.
-/

namespace Jellium

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure CoulombForm (V : Type*) [AddCommGroup V] [Module ℝ V] where
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symmetric : ∀ f g, form f g = form g f
  nonnegative : ∀ f, 0 ≤ form f f

namespace CoulombForm

variable (D : CoulombForm V)

def indirect (kinetic repulsion : ℝ) (density : V) : ℝ :=
  kinetic + repulsion - D.form density density

def jellium (kinetic repulsion : ℝ) (density background : V) : ℝ :=
  kinetic + repulsion - 2 * D.form density background + D.form background background

/-- Equation `eq:conj_identity`, with the factor one half already in `D`. -/
theorem jellium_eq_indirect_add_charge
    (kinetic repulsion : ℝ) (density background : V) :
    D.jellium kinetic repulsion density background =
      D.indirect kinetic repulsion density +
        D.form (density - background) (density - background) := by
  simp only [jellium, indirect, map_sub, LinearMap.sub_apply]
  rw [D.symmetric background density]
  ring

/-- Positivity gives the correct direction after fixed-background averaging. -/
theorem indirect_le_jellium
    (kinetic repulsion : ℝ) (density background : V) :
    D.indirect kinetic repulsion density ≤
      D.jellium kinetic repulsion density background := by
  rw [D.jellium_eq_indirect_add_charge]
  exact le_add_of_nonneg_right (D.nonnegative _)

/-- Coulomb self-energy is additive when all the cross terms vanish. -/
theorem self_sum {ι : Type*} (s : Finset ι) (charge : ι → V)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → D.form (charge i) (charge j) = 0) :
    D.form (∑ i ∈ s, charge i) (∑ i ∈ s, charge i) =
      ∑ i ∈ s, D.form (charge i) (charge i) := by
  classical
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_eq_single i
    (fun j hj hji => hcross j hj i hi hji)
    (fun h => (h hi).elim)

/-- The exact core-plus-fluid identity underlying `eq:upper_exact_identity`.

The product-state theorem from Fock-space theory supplies `hproduct`.
Newton's theorem and the support geometry must supply the three zero-cross
hypotheses. They are not proved or silently postulated here.
-/
theorem core_fluid_identity {ι : Type*} (s : Finset ι)
    (core collar : ι → V) (coreIndirect : ι → ℝ)
    (fluidIndirect totalJ : ℝ)
    (hcore : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → D.form (core i) (core j) = 0)
    (hcollar : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → D.form (collar i) (collar j) = 0)
    (hmixed : ∀ i ∈ s, ∀ j ∈ s, D.form (core i) (collar j) = 0)
    (hproduct : totalJ = (∑ i ∈ s, coreIndirect i) + fluidIndirect +
      D.form ((∑ i ∈ s, core i) + ∑ i ∈ s, collar i)
        ((∑ i ∈ s, core i) + ∑ i ∈ s, collar i)) :
    totalJ = (∑ i ∈ s, (coreIndirect i + D.form (core i) (core i))) +
      fluidIndirect + ∑ i ∈ s, D.form (collar i) (collar i) := by
  have hzero : D.form (∑ i ∈ s, core i) (∑ i ∈ s, collar i) = 0 := by
    simp only [map_sum, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    exact Finset.sum_eq_zero (fun j hj => hmixed j hj i hi)
  have hzero' : D.form (∑ i ∈ s, collar i) (∑ i ∈ s, core i) = 0 := by
    rw [D.symmetric]
    exact hzero
  rw [hproduct]
  simp only [map_add, LinearMap.add_apply]
  rw [hzero, hzero', D.self_sum s core hcore, D.self_sum s collar hcollar]
  rw [Finset.sum_add_distrib]
  ring

/-- A finite mixture version of affinity at a fixed background.
This checks the exact background and all coefficients, without an assertion
about Bochner integration of the continuum family of states.
-/
theorem fixed_background_affinity {ι : Type*} (s : Finset ι)
    (weight kinetic repulsion : ι → ℝ) (density : ι → V) (background : V)
    (hmass : ∑ i ∈ s, weight i = 1) :
    D.jellium (∑ i ∈ s, weight i * kinetic i)
      (∑ i ∈ s, weight i * repulsion i)
      (∑ i ∈ s, weight i • density i) background =
    ∑ i ∈ s, weight i * D.jellium (kinetic i) (repulsion i) (density i) background := by
  simp only [jellium, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  have hconstant : (∑ i ∈ s, weight i * D.form background background) =
      D.form background background := by
    rw [← Finset.sum_mul, hmass, one_mul]
  have hcross : (∑ i ∈ s, weight i * (2 * D.form (density i) background)) =
      2 * ∑ i ∈ s, weight i * D.form (density i) background := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hconstant, hcross]
  simp only [mul_add, Finset.sum_add_distrib]

end CoulombForm
end Jellium
