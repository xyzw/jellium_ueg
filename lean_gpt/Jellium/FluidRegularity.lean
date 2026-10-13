import Jellium.Gluing
import Jellium.TrialState
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Sobolev regularity of the core-plus-fluid density is a consequence of
square-root gluing, not an assumed property of the trial construction. -/

open Set Finset

namespace Jellium.TrialState.FluidGeometry

universe u v
variable {X : Type u} [MeasurableSpace X]
variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable {C : ChargeModel X V} {n : ℕ} {ρ H : ℝ}

/-- Pointwise realization of the actual fluid by the glued radial profiles. -/
theorem eval_fluid_eq_gluedDensity
    (G : FluidGeometry C n ρ H) (hρ : 0 ≤ ρ)
    (profile : Fin n → X → ℝ)
    (hcore : ∀ i x, x ∈ G.core i → profile i x = 0)
    (hcollar : ∀ i x, x ∉ G.core i →
      C.eval (G.collar i) x = ρ * (profile i x ^ 2 - 1)) :
    C.eval G.fluid = Gluing.gluedDensity Finset.univ
      (fun x => Real.sqrt (C.eval G.background x)) (Real.sqrt ρ) profile := by
  funext x
  rw [G.fluid_eval]
  simp only [Gluing.gluedDensity, Real.sq_sqrt (G.background_nonneg x), Real.sq_sqrt hρ]
  have hlocal (i : Fin n) :
      ρ * (profile i x ^ 2 - 1) = -C.eval (G.coreBackground i) x + C.eval (G.collar i) x := by
    by_cases hx : x ∈ G.core i
    · rw [hcore i x hx, G.core_on i x hx, G.collar_core i x hx]
      ring
    · rw [hcollar i x hx, G.core_off i x hx]
      ring
  simp_rw [hlocal, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/-- Standard Sobolev additivity now gives regularity of the constructed fluid.
The local premises concern the explicit smooth compact corrections only. -/
theorem sqrt_fluid_mem
    (G : FluidGeometry C n ρ H) (hρ : 0 ≤ ρ)
    (H1 : Submodule ℝ (X → ℝ))
    (profile : Fin n → X → ℝ)
    (hprofile : ∀ i x, 0 ≤ profile i x)
    (houtside : ∀ i x, x ∉ G.enlarged i → profile i x = 1)
    (hcore : ∀ i x, x ∈ G.core i → profile i x = 0)
    (hcollar : ∀ i x, x ∉ G.core i →
      C.eval (G.collar i) x = ρ * (profile i x ^ 2 - 1))
    (hbackground : (fun x => Real.sqrt (C.eval G.background x)) ∈ H1)
    (hcorrection : ∀ i, (fun x => Real.sqrt ρ * (profile i x - 1)) ∈ H1) :
    (fun x => Real.sqrt (C.eval G.fluid x)) ∈ H1 := by
  rw [G.eval_fluid_eq_gluedDensity hρ profile hcore hcollar]
  apply Gluing.sqrt_gluedDensity_mem H1 Finset.univ G.enlarged
    (fun x => Real.sqrt (C.eval G.background x)) (Real.sqrt ρ) profile
  · intro i _ j _ hij
    exact G.disjoint hij
  · exact fun x => Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _
  · exact fun i _ x => hprofile i x
  · exact fun i _ x hx => houtside i x hx
  · intro i _ x hx
    rw [G.plateau i x hx]
  · exact hbackground
  · exact fun i _ => hcorrection i

end Jellium.TrialState.FluidGeometry
