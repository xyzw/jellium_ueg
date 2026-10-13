import Jellium.Electrostatics
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Finite core-plus-fluid trial states.

Charges belong to a real vector space embedded in actual functions. Thus no
Coulomb energy is asserted for arbitrary, possibly nonintegrable functions.
The state interface below contains only standard quasifree and disjoint Fock
product laws. The spatial density, support and electrostatic cancellation
arguments are proved from pointwise core and collar data.
-/

open MeasureTheory Set Finset

namespace Jellium.TrialState

universe u v w
variable {X : Type u} [MeasurableSpace X]
variable {V : Type v} [AddCommGroup V] [Module ℝ V]

structure ChargeModel (X : Type u) [MeasurableSpace X]
    (V : Type v) [AddCommGroup V] [Module ℝ V] where
  eval : V →ₗ[ℝ] (X → ℝ)
  eval_injective : Function.Injective eval
  measure : Measure X
  mass : V →ₗ[ℝ] ℝ
  mass_integral : ∀ f, mass f = ∫ x, eval f x ∂measure
  coulomb : CoulombForm V
  potential : V → (X → ℝ)
  coulomb_integral : ∀ f g,
    coulomb.form f g = (1 / 2 : ℝ) * ∫ x, potential f x * eval g x ∂measure

variable (C : ChargeModel X V)

structure FluidGeometry (n : ℕ) (ρ H : ℝ) where
  background : V
  coreBackground : Fin n → V
  collar : Fin n → V
  core : Fin n → Set X
  enlarged : Fin n → Set X
  core_subset : ∀ i, core i ⊆ enlarged i
  disjoint : Pairwise fun i j => Disjoint (enlarged i) (enlarged j)
  background_nonneg : ∀ x, 0 ≤ C.eval background x
  background_le : ∀ x, C.eval background x ≤ ρ
  plateau : ∀ i x, x ∈ enlarged i → C.eval background x = ρ
  core_on : ∀ i x, x ∈ core i → C.eval (coreBackground i) x = ρ
  core_off : ∀ i x, x ∉ core i → C.eval (coreBackground i) x = 0
  collar_outside : ∀ i x, x ∉ enlarged i → C.eval (collar i) x = 0
  collar_core : ∀ i x, x ∈ core i → C.eval (collar i) x = 0
  collar_profile : ∀ i x, x ∈ enlarged i → x ∉ core i →
    0 ≤ ρ + C.eval (collar i) x ∧ ρ + C.eval (collar i) x ≤ H * ρ
  collar_neutral : ∀ i, C.mass (collar i) = 0

namespace FluidGeometry

variable {C} {n : ℕ} {ρ H : ℝ} (G : FluidGeometry C n ρ H)

def fluid : V := G.background - ∑ i, G.coreBackground i + ∑ i, G.collar i

theorem fluid_eval (x : X) :
    C.eval G.fluid x = C.eval G.background x -
      ∑ i, C.eval (G.coreBackground i) x + ∑ i, C.eval (G.collar i) x := by
  simp only [fluid, map_add, map_sub, map_sum, Pi.add_apply, Pi.sub_apply, Finset.sum_apply]

theorem outside_other {i j : Fin n} (hij : i ≠ j) {x : X}
    (hx : x ∈ G.enlarged i) : x ∉ G.enlarged j := by
  intro hj
  exact Set.disjoint_left.1 (G.disjoint hij) hx hj

theorem core_sum_at {i : Fin n} {x : X} (hx : x ∈ G.enlarged i) :
    (∑ j, C.eval (G.coreBackground j) x) = C.eval (G.coreBackground i) x := by
  classical
  apply Finset.sum_eq_single i
  · intro j _ hji
    apply G.core_off
    intro hj
    exact G.outside_other (Ne.symm hji) hx (G.core_subset j hj)
  · simp

theorem collar_sum_at {i : Fin n} {x : X} (hx : x ∈ G.enlarged i) :
    (∑ j, C.eval (G.collar j) x) = C.eval (G.collar i) x := by
  classical
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact G.collar_outside j x (G.outside_other (Ne.symm hji) hx)
  · simp

theorem fluid_on_core {i : Fin n} {x : X} (hx : x ∈ G.core i) :
    C.eval G.fluid x = 0 := by
  have hB := G.core_subset i hx
  rw [G.fluid_eval, G.core_sum_at hB, G.collar_sum_at hB,
    G.plateau i x hB, G.core_on i x hx, G.collar_core i x hx]
  ring

theorem fluid_on_shell {i : Fin n} {x : X}
    (hx : x ∈ G.enlarged i) (hcore : x ∉ G.core i) :
    C.eval G.fluid x = ρ + C.eval (G.collar i) x := by
  rw [G.fluid_eval, G.core_sum_at hx, G.collar_sum_at hx,
    G.plateau i x hx, G.core_off i x hcore]
  ring

theorem fluid_outside {x : X} (hx : ∀ i, x ∉ G.enlarged i) :
    C.eval G.fluid x = C.eval G.background x := by
  rw [G.fluid_eval]
  have hq : (∑ i, C.eval (G.coreBackground i) x) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact G.core_off i x (fun hi => hx i (G.core_subset i hi))
  have hg : (∑ i, C.eval (G.collar i) x) = 0 := by
    exact Finset.sum_eq_zero (fun i _ => G.collar_outside i x (hx i))
  rw [hq, hg]
  ring

theorem fluid_bounds (hρ : 0 ≤ ρ) (hH : 1 ≤ H) (x : X) :
    0 ≤ C.eval G.fluid x ∧ C.eval G.fluid x ≤ H * ρ := by
  classical
  by_cases hx : ∃ i, x ∈ G.enlarged i
  · obtain ⟨i, hi⟩ := hx
    by_cases hcore : x ∈ G.core i
    · rw [G.fluid_on_core hcore]
      constructor
      · exact le_rfl
      · positivity
    · rw [G.fluid_on_shell hi hcore]
      exact G.collar_profile i x hi hcore
  · have hout : ∀ i, x ∉ G.enlarged i := fun i hi => hx ⟨i, hi⟩
    rw [G.fluid_outside hout]
    exact ⟨G.background_nonneg x, le_trans (G.background_le x) (by nlinarith)⟩

theorem fluid_mass : C.mass G.fluid =
    C.mass G.background - ∑ i, C.mass (G.coreBackground i) := by
  simp [fluid, map_add, map_sub, map_sum, G.collar_neutral]

end FluidGeometry

/-- The ordinary Coulomb potential pairing makes separated supports interact
trivially. This proof uses the actual product integrand. -/
theorem coulomb_zero_of_potential_support
    (f g : V) (A : Set X)
    (hpotential : ∀ x, x ∉ A → C.potential f x = 0)
    (hcharge : ∀ x, x ∈ A → C.eval g x = 0) :
    C.coulomb.form f g = 0 := by
  rw [C.coulomb_integral]
  have hzero : (fun x => C.potential f x * C.eval g x) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ A
    · rw [hcharge x hx, mul_zero]
    · rw [hpotential x hx, zero_mul]
  rw [hzero, integral_zero, mul_zero]

theorem support_cancellations
    {n : ℕ} {ρ H : ℝ} (G : FluidGeometry C n ρ H) (d : Fin n → V)
    (hd : ∀ i, Function.support (C.eval (d i)) ⊆ G.core i)
    (hcoreNewton : ∀ i x, x ∉ G.core i →
      C.potential (d i - G.coreBackground i) x = 0)
    (hcollarNewton : ∀ i x, x ∉ G.enlarged i → C.potential (G.collar i) x = 0) :
    (∀ i j, i ≠ j → C.coulomb.form
      (d i - G.coreBackground i) (d j - G.coreBackground j) = 0) ∧
    (∀ i j, i ≠ j → C.coulomb.form (G.collar i) (G.collar j) = 0) ∧
    (∀ i j, C.coulomb.form (d i - G.coreBackground i) (G.collar j) = 0) := by
  classical
  have hd_off : ∀ i x, x ∉ G.core i → C.eval (d i) x = 0 := by
    intro i x hx
    by_contra hn
    exact hx (hd i hn)
  have hf_off : ∀ i x, x ∉ G.core i → C.eval (d i - G.coreBackground i) x = 0 := by
    intro i x hx
    simp only [map_sub, Pi.sub_apply, hd_off i x hx, G.core_off i x hx, sub_self]
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    apply coulomb_zero_of_potential_support C _ _ (G.core i) (hcoreNewton i)
    intro x hx
    apply hf_off
    intro hj
    exact G.outside_other hij (G.core_subset i hx) (G.core_subset j hj)
  · intro i j hij
    apply coulomb_zero_of_potential_support C _ _ (G.enlarged i) (hcollarNewton i)
    intro x hx
    exact G.collar_outside j x (G.outside_other hij hx)
  · intro i j
    apply coulomb_zero_of_potential_support C _ _ (G.core i) (hcoreNewton i)
    intro x hx
    by_cases hij : i = j
    · subst j
      exact G.collar_core i x hx
    · exact G.collar_outside j x (G.outside_other hij (G.core_subset i hx))

/-- Standard state operations. `regular` is the density representability
condition `sqrt p ∈ H¹`, and `gradient p` is its Dirichlet integral. They remain
explicit so that the actual analytic collar construction must discharge them.
The repulsion law is the usual disjoint-product cross interaction, written as
the total direct term minus the sum of its diagonal terms. -/
structure StateAPI (State : Type w) (h₂ cTF : ℝ) where
  density : State → V
  kinetic : State → ℝ
  repulsion : State → ℝ
  regular : V → Prop
  gradient : V → ℝ
  product : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (factors : ι → State),
    Pairwise (fun i j => Disjoint (Function.support (C.eval (density (factors i))))
      (Function.support (C.eval (density (factors j))))) →
    ∃ Γ : State,
      density Γ = ∑ i, density (factors i) ∧
      kinetic Γ = ∑ i, kinetic (factors i) ∧
      repulsion Γ = (∑ i, repulsion (factors i)) +
        C.coulomb.form (∑ i, density (factors i)) (∑ i, density (factors i)) -
        ∑ i, C.coulomb.form (density (factors i)) (density (factors i))
  quasifree : ∀ (p : V) (M : ℝ), 0 < M → regular p →
    (∀ x, 0 ≤ C.eval p x ∧ C.eval p x ≤ M) →
    ∃ Γ : State, density Γ = p ∧
      C.coulomb.indirect (h₂ * kinetic Γ) (repulsion Γ) (density Γ) ≤
        h₂ * gradient p + h₂ * cTF * M ^ ((2 : ℝ) / 3) * C.mass p

namespace StateAPI

variable {C} {State : Type w} {h₂ cTF : ℝ} (S : StateAPI C State h₂ cTF)

def indirect (Γ : State) : ℝ :=
  C.coulomb.indirect (h₂ * S.kinetic Γ) (S.repulsion Γ) (S.density Γ)

def jellium (Γ : State) (background : V) : ℝ :=
  C.coulomb.jellium (h₂ * S.kinetic Γ) (S.repulsion Γ) (S.density Γ) background

theorem product_indirect
    (ι : Type) [Fintype ι] [DecidableEq ι] (factors : ι → State)
    (hdisjoint : Pairwise (fun i j =>
      Disjoint (Function.support (C.eval (S.density (factors i))))
        (Function.support (C.eval (S.density (factors j)))))) :
    ∃ Γ : State, S.density Γ = ∑ i, S.density (factors i) ∧
      S.indirect Γ = ∑ i, S.indirect (factors i) := by
  obtain ⟨Γ, hd, hT, hW⟩ := S.product ι factors hdisjoint
  refine ⟨Γ, hd, ?_⟩
  simp only [indirect, CoulombForm.indirect]
  rw [hd, hT, hW]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- This constructs both the quasifree fluid and the complete finite product.
Neither trial existence nor a trial-energy bound occurs among its premises. -/
theorem assemble_product
    {n : ℕ} {ρ H M : ℝ} (G : FluidGeometry C n ρ H) (cores : Fin n → State)
    (hρ : 0 ≤ ρ) (hH : 1 ≤ H) (hM : 0 < M) (hcap : H * ρ ≤ M)
    (hregular : S.regular G.fluid)
    (hsupport : ∀ i, Function.support (C.eval (S.density (cores i))) ⊆ G.core i) :
    ∃ Φ Γ : State,
      S.density Φ = G.fluid ∧
      S.density Γ = G.background +
        (∑ i, (S.density (cores i) - G.coreBackground i)) + ∑ i, G.collar i ∧
      S.indirect Γ = (∑ i, S.indirect (cores i)) + S.indirect Φ ∧
      S.indirect Φ ≤ h₂ * S.gradient G.fluid +
        h₂ * cTF * M ^ ((2 : ℝ) / 3) * C.mass G.fluid := by
  classical
  have hbounds : ∀ x, 0 ≤ C.eval G.fluid x ∧ C.eval G.fluid x ≤ M := by
    intro x
    exact ⟨(G.fluid_bounds hρ hH x).1, le_trans (G.fluid_bounds hρ hH x).2 hcap⟩
  obtain ⟨Φ, hΦdensity, hΦenergy⟩ := S.quasifree G.fluid M hM hregular hbounds
  have hfluid_core : ∀ i,
      Disjoint (Function.support (C.eval (S.density Φ)))
        (Function.support (C.eval (S.density (cores i)))) := by
    intro i
    apply Set.disjoint_left.2
    intro x hΦ hcore
    have hzero := G.fluid_on_core (hsupport i hcore)
    rw [← hΦdensity] at hzero
    exact hΦ hzero
  have hcores : Pairwise fun i j =>
      Disjoint (Function.support (C.eval (S.density (cores i))))
        (Function.support (C.eval (S.density (cores j)))) := by
    intro i j hij
    exact (G.disjoint hij).mono
      (Set.Subset.trans (hsupport i) (G.core_subset i))
      (Set.Subset.trans (hsupport j) (G.core_subset j))
  let factors : Option (Fin n) → State := fun o => o.elim Φ cores
  have hfactor : Pairwise fun i j =>
      Disjoint (Function.support (C.eval (S.density (factors i))))
        (Function.support (C.eval (S.density (factors j)))) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hfluid_core j
    | some i =>
      cases j with
      | none => exact (hfluid_core i).symm
      | some j => exact hcores (fun h => hij (congrArg some h))
  obtain ⟨Γ, hΓdensity, hΓenergy⟩ := S.product_indirect (Option (Fin n)) factors hfactor
  have hdensity : S.density Γ = G.background +
      (∑ i, (S.density (cores i) - G.coreBackground i)) + ∑ i, G.collar i := by
    rw [hΓdensity, Fintype.sum_option]
    change S.density Φ + (∑ i, S.density (cores i)) = _
    rw [hΦdensity]
    simp only [FluidGeometry.fluid, Finset.sum_sub_distrib]
    abel
  have henergy : S.indirect Γ = (∑ i, S.indirect (cores i)) + S.indirect Φ := by
    rw [hΓenergy, Fintype.sum_option]
    change S.indirect Φ + (∑ i, S.indirect (cores i)) = _
    ring
  exact ⟨Φ, Γ, hΦdensity, hdensity, henergy, hΦenergy⟩

/-- Exact finite trial identity, with every vanished Coulomb interaction
deduced from the spatial supports and Newton potentials. -/
theorem assemble_trial
    {n : ℕ} {ρ H M : ℝ} (G : FluidGeometry C n ρ H) (cores : Fin n → State)
    (hρ : 0 ≤ ρ) (hH : 1 ≤ H) (hM : 0 < M) (hcap : H * ρ ≤ M)
    (hregular : S.regular G.fluid)
    (hsupport : ∀ i, Function.support (C.eval (S.density (cores i))) ⊆ G.core i)
    (hcoreNewton : ∀ i x, x ∉ G.core i →
      C.potential (S.density (cores i) - G.coreBackground i) x = 0)
    (hcollarNewton : ∀ i x, x ∉ G.enlarged i → C.potential (G.collar i) x = 0) :
    ∃ Φ Γ : State,
      S.density Φ = G.fluid ∧
      S.density Γ = G.background +
        (∑ i, (S.density (cores i) - G.coreBackground i)) + ∑ i, G.collar i ∧
      S.jellium Γ G.background =
        (∑ i, S.jellium (cores i) (G.coreBackground i)) + S.indirect Φ +
          ∑ i, C.coulomb.form (G.collar i) (G.collar i) ∧
      S.indirect Φ ≤ h₂ * S.gradient G.fluid +
        h₂ * cTF * M ^ ((2 : ℝ) / 3) * C.mass G.fluid := by
  obtain ⟨Φ, Γ, hΦd, hΓd, hΓenergy, hΦenergy⟩ :=
    S.assemble_product G cores hρ hH hM hcap hregular hsupport
  obtain ⟨hcore, hcollar, hmixed⟩ :=
    support_cancellations C G (fun i => S.density (cores i)) hsupport hcoreNewton hcollarNewton
  let f : Fin n → V := fun i => S.density (cores i) - G.coreBackground i
  have hcharge : S.density Γ - G.background = (∑ i, f i) + ∑ i, G.collar i := by
    rw [hΓd]
    dsimp [f]
    abel
  have hproduct : S.jellium Γ G.background =
      (∑ i, S.indirect (cores i)) + S.indirect Φ +
        C.coulomb.form ((∑ i, f i) + ∑ i, G.collar i)
          ((∑ i, f i) + ∑ i, G.collar i) := by
    unfold jellium
    rw [C.coulomb.jellium_eq_indirect_add_charge, hcharge]
    change S.indirect Γ + _ = _
    rw [hΓenergy]
  have hidentity := C.coulomb.core_fluid_identity Finset.univ f G.collar
    (fun i => S.indirect (cores i)) (S.indirect Φ) (S.jellium Γ G.background)
    (fun i _ j _ hij => hcore i j hij)
    (fun i _ j _ hij => hcollar i j hij)
    (fun i _ j _ => hmixed i j) hproduct
  have hcoreJ : ∀ i, S.indirect (cores i) + C.coulomb.form (f i) (f i) =
      S.jellium (cores i) (G.coreBackground i) := by
    intro i
    exact (C.coulomb.jellium_eq_indirect_add_charge
      (h₂ * S.kinetic (cores i)) (S.repulsion (cores i))
      (S.density (cores i)) (G.coreBackground i)).symm
  simp_rw [hcoreJ] at hidentity
  exact ⟨Φ, Γ, hΦd, hΓd, hidentity, hΦenergy⟩

theorem assembled_mass
    {n : ℕ} {ρ H : ℝ} (G : FluidGeometry C n ρ H)
    (cores : Fin n → State) (Γ : State)
    (hdensity : S.density Γ = G.background +
      (∑ i, (S.density (cores i) - G.coreBackground i)) + ∑ i, G.collar i)
    (hneutral : ∀ i, C.mass (S.density (cores i)) = C.mass (G.coreBackground i)) :
    C.mass (S.density Γ) = C.mass G.background := by
  rw [hdensity]
  simp [map_add, map_sum, map_sub, hneutral, G.collar_neutral]

/-- Quantitative upper trial from the standard state primitives and the actual
fluid construction. The core and collar bounds are individual local bounds,
not a presumed global trial inequality. -/
theorem assemble_upper_trial
    {n : ℕ} {ρ H M : ℝ} (G : FluidGeometry C n ρ H) (cores : Fin n → State)
    (hρ : 0 ≤ ρ) (hH : 1 ≤ H) (hM : 0 < M) (hcap : H * ρ ≤ M)
    (hregular : S.regular G.fluid)
    (hsupport : ∀ i, Function.support (C.eval (S.density (cores i))) ⊆ G.core i)
    (hcoreNewton : ∀ i x, x ∉ G.core i →
      C.potential (S.density (cores i) - G.coreBackground i) x = 0)
    (hcollarNewton : ∀ i x, x ∉ G.enlarged i → C.potential (G.collar i) x = 0)
    (hneutral : ∀ i, C.mass (S.density (cores i)) = C.mass (G.coreBackground i))
    (coreUpper collarUpper : Fin n → ℝ)
    (hcoreUpper : ∀ i, S.jellium (cores i) (G.coreBackground i) ≤ coreUpper i)
    (hcollarUpper : ∀ i, C.coulomb.form (G.collar i) (G.collar i) ≤ collarUpper i) :
    ∃ Γ : State,
      S.density Γ = G.background +
        (∑ i, (S.density (cores i) - G.coreBackground i)) + ∑ i, G.collar i ∧
      C.mass (S.density Γ) = C.mass G.background ∧
      S.jellium Γ G.background ≤ (∑ i, coreUpper i) +
        (h₂ * S.gradient G.fluid +
          h₂ * cTF * M ^ ((2 : ℝ) / 3) * C.mass G.fluid) + ∑ i, collarUpper i := by
  obtain ⟨Φ, Γ, _hΦd, hΓd, hidentity, hΦenergy⟩ :=
    S.assemble_trial G cores hρ hH hM hcap hregular hsupport hcoreNewton hcollarNewton
  refine ⟨Γ, hΓd, S.assembled_mass G cores Γ hΓd hneutral, ?_⟩
  rw [hidentity]
  have hc := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin n))) => hcoreUpper i)
  have hg := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin n))) => hcollarUpper i)
  linarith

end StateAPI

end Jellium.TrialState
