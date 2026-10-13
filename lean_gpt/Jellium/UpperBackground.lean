import Jellium.SmoothCube
import Jellium.UpperConstruction
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual fixed-kernel smeared cubic backgrounds. The charge representative,
mass, plateau, support, Sobolev membership and surface Dirichlet bound are
constructed. The potential input is the ordinary boundedness of the Coulomb
potential of any bounded integrable compactly supported charge. -/

open Set Metric MeasureTheory
open scoped ContDiff

namespace Jellium.UpperBackground

abbrev Space := Spatial.Space

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℝ V] {State : Type v}
variable (C : TrialState.ChargeModel Space V) {h₂ cTF sf : ℝ}
variable (S : TrialState.StateAPI C State h₂ cTF)
variable (D : UpperConstruction.SobolevDirichlet C S sf)

/-- A general standard Coulomb fact, not a statement about the constructed
background or its scale. -/
def BoundedPotentialLaw : Prop :=
  ∀ f : V, Integrable (C.eval f) C.measure → HasCompactSupport (C.eval f) →
    (∃ M : ℝ, ∀ x, |C.eval f x| ≤ M) →
    ∃ P : ℝ, 0 ≤ P ∧ ∀ x, |C.potential f x| ≤ P

/-- The background exists for every real box parameter. Its positive-volume
mass formula and surface estimate state their appropriate size conditions. -/
structure Data (χ : Space → ℝ) (ρ R a : ℝ) (β : V) : Prop where
  eval : C.eval β = SmoothCube.smooth ρ R χ
  mass : 0 ≤ R → C.mass β = ρ * R ^ 3
  integrable : Integrable (C.eval β) C.measure
  compact : HasCompactSupport (C.eval β)
  bounds : ∀ x, 0 ≤ C.eval β x ∧ C.eval β x ≤ ρ
  support : Function.support (C.eval β) ⊆ Spatial.cube (R + 2 * a)
  plateau : ∀ x, x ∈ Spatial.cube (R - 2 * a) → C.eval β x = ρ
  root_mem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1
  regular : S.regular β
  gradient : 2 * a ≤ R → S.gradient β ≤
    16 * ρ * (∫ x, SmoothCube.fisherDensity χ x) * R ^ 2 * a
  potential : ∃ P : ℝ, 0 ≤ P ∧ ∀ x, |C.potential β x| ≤ P

variable {C S D}

theorem kernel_compact {χ : Space → ℝ} {a : ℝ}
    (hsupport : Function.support χ ⊆ closedBall 0 a) : HasCompactSupport χ := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) a)
  intro x hx
  by_contra hn
  exact hx (hsupport hn)

theorem kernel_continuous {χ : Space → ℝ}
    (hχ : ∀ x, 0 ≤ χ x) (hroot : ContDiff ℝ ∞ (fun x => Real.sqrt (χ x))) :
    Continuous χ := by
  have h := hroot.continuous.pow 2
  change Continuous (fun x => Real.sqrt (χ x) ^ 2) at h
  have heq : (fun x => Real.sqrt (χ x) ^ 2) = χ := funext (fun x => Real.sq_sqrt (hχ x))
  rwa [heq] at h

theorem kernel_root_compact {χ : Space → ℝ} {a : ℝ}
    (hsupport : Function.support χ ⊆ closedBall 0 a) :
    HasCompactSupport (fun x => Real.sqrt (χ x)) :=
  (kernel_compact hsupport).comp_left Real.sqrt_zero

theorem kernel_fisher_integrable {χ : Space → ℝ} {a : ℝ}
    (hsupport : Function.support χ ⊆ closedBall 0 a)
    (hroot : ContDiff ℝ ∞ (fun x => Real.sqrt (χ x))) :
    Integrable (SmoothCube.fisherDensity χ) := by
  have hc : Continuous (SmoothCube.fisherDensity χ) :=
    (hroot.continuous_fderiv (by simp)).norm.pow 2
  have hd : HasCompactSupport (fderiv ℝ (fun x : Space => Real.sqrt (χ x))) :=
    (kernel_root_compact hsupport).fderiv ℝ
  have hs : HasCompactSupport (SmoothCube.fisherDensity χ) := by
    change HasCompactSupport (fun x => ‖fderiv ℝ (fun y : Space => Real.sqrt (χ y)) x‖ ^ 2)
    exact hd.comp_left (g := fun L : Space →L[ℝ] ℝ => ‖L‖ ^ 2) (by simp)
  exact hc.integrable_of_hasCompactSupport hs

/-- A charge representative with all background data is built from the actual
convolution for every R. No β, mass identity, regularity or surface bound is
supplied by the caller. -/
theorem exists_data (C : TrialState.ChargeModel Space V)
    (S : TrialState.StateAPI C State h₂ cTF) (D : UpperConstruction.SobolevDirichlet C S sf)
    (hmeasure : C.measure = volume) (represent : UpperConstruction.Representations C)
    (potential : BoundedPotentialLaw C)
    (sobolev : SmoothCube.ConvolutionSobolevLaws D.H1 D.energy)
    {χ : Space → ℝ} {ρ a : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a)
    (hχ : ∀ x, 0 ≤ χ x) (hmass : ∫ x, χ x = 1)
    (hsupport : Function.support χ ⊆ closedBall 0 a)
    (hroot : ContDiff ℝ ∞ (fun x => Real.sqrt (χ x))) (R : ℝ) :
    ∃ β : V, Data C S D χ ρ R a β := by
  have hiχ : Integrable χ :=
    (kernel_continuous hχ hroot).integrable_of_hasCompactSupport (kernel_compact hsupport)
  have hrootmem := D.smooth_mem _ hroot (kernel_root_compact hsupport)
  have hfish := kernel_fisher_integrable hsupport hroot
  have hβint : Integrable (SmoothCube.smooth ρ R χ) C.measure := by
    rw [hmeasure]
    exact SmoothCube.smooth_integrable ρ R χ hiχ
  have hβcompact := SmoothCube.smooth_compact (ρ := ρ) (R := R) χ hsupport
  have hβbounds (x : Space) :
      0 ≤ SmoothCube.smooth ρ R χ x ∧ SmoothCube.smooth ρ R χ x ≤ ρ :=
    ⟨SmoothCube.smooth_nonneg χ hρ hχ x, SmoothCube.smooth_le χ hρ hχ hiχ hmass x⟩
  have hβabs : ∃ M : ℝ, ∀ x, |SmoothCube.smooth ρ R χ x| ≤ M := by
    refine ⟨ρ, fun x => ?_⟩
    rw [abs_of_nonneg (hβbounds x).1]
    exact (hβbounds x).2
  obtain ⟨β, heval⟩ := represent _ hβint hβcompact hβabs
  have hsqrt : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1 := by
    rw [heval]
    exact (sobolev.convolution χ (SmoothCube.sharp ρ R) ρ hρ
      (fun x => ⟨SmoothCube.sharp_nonneg hρ x, SmoothCube.sharp_le hρ x⟩)
      (SmoothCube.sharp_integrable ρ R) hχ hiχ hmass hrootmem hroot hfish).1
  have hregular := (D.regular_iff β).2 hsqrt
  refine ⟨β, heval, ?_, heval ▸ hβint, heval ▸ hβcompact, ?_, ?_, ?_, hsqrt, hregular, ?_, ?_⟩
  · intro hR
    rw [C.mass_integral, heval, hmeasure]
    exact SmoothCube.smooth_mass ρ hR χ hiχ hmass
  · intro x
    rw [heval]
    exact hβbounds x
  · rw [heval]
    exact SmoothCube.smooth_support χ hsupport
  · intro x hx
    rw [heval]
    exact SmoothCube.smooth_plateau χ hmass hsupport hx
  · intro hsize
    rw [D.gradient_eq β hregular, heval]
    exact (SmoothCube.smooth_fisher_surface_bound D.H1 D.energy sobolev hρ ha hsize χ
      hχ hiχ hmass hsupport hrootmem hroot hfish).2
  · apply potential β
    · rwa [heval]
    · rwa [heval]
    · rwa [heval]

end Jellium.UpperBackground
