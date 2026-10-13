import Jellium.Spatial
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual smoothed cubic backgrounds and their surface-order Fisher bound.
Convolution support and mass are proved directly. The only Sobolev input is
the ordinary Hoffmann--Ostenhof convolution inequality for arbitrary bounded
nonnegative inputs, stated below independently of cubes. -/

open Set Metric MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff
open Classical

namespace Jellium.SmoothCube

open Spatial

noncomputable def sharp (ρ R : ℝ) : Space → ℝ :=
  (cube R).indicator (fun _ => ρ)

noncomputable def smooth (ρ R : ℝ) (χ : Space → ℝ) : Space → ℝ :=
  χ ⋆[lsmul ℝ ℝ] sharp ρ R

noncomputable def fisherDensity (f : Space → ℝ) (x : Space) : ℝ :=
  ‖fderiv ℝ (fun y => Real.sqrt (f y)) x‖ ^ 2

theorem sharp_nonneg {ρ R : ℝ} (hρ : 0 ≤ ρ) (x : Space) : 0 ≤ sharp ρ R x := by
  by_cases hx : x ∈ cube R <;> simp [sharp, hx, hρ]

theorem sharp_le {ρ R : ℝ} (hρ : 0 ≤ ρ) (x : Space) : sharp ρ R x ≤ ρ := by
  by_cases hx : x ∈ cube R <;> simp [sharp, hx, hρ]

theorem sharp_support (ρ R : ℝ) : Function.support (sharp ρ R) ⊆ cube R := by
  intro x hx
  by_contra hnot
  exact hx (by simp [sharp, hnot])

/-- Bounded cube support yields genuine compact support in Euclidean space. -/
theorem compactSupport_of_cube_support {f : Space → ℝ} {R : ℝ}
    (hsupp : Function.support f ⊆ cube R) : HasCompactSupport f := by
  let K : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-(R / 2)) (R / 2))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  apply HasCompactSupport.intro (hK.image (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)))
  intro x hx
  by_contra hne
  apply hx
  refine ⟨WithLp.ofLp x, ?_, rfl⟩
  intro k _
  have hk := abs_lt.mp (hsupp hne k)
  exact ⟨hk.1.le, hk.2.le⟩

theorem sharp_compact (ρ R : ℝ) : HasCompactSupport (sharp ρ R) :=
  compactSupport_of_cube_support (sharp_support ρ R)

theorem sharp_integrable (ρ R : ℝ) : Integrable (sharp ρ R) :=
  (integrableOn_const (volume_cube_ne_top R)).integrable_indicator (measurableSet_cube R)

theorem sharp_mass (ρ : ℝ) {R : ℝ} (hR : 0 ≤ R) : ∫ x, sharp ρ R x = ρ * R ^ 3 := by
  rw [sharp, integral_indicator (measurableSet_cube R), setIntegral_const]
  simp only [smul_eq_mul, measureReal_def, volume_cube_toReal hR]
  ring

theorem smooth_nonneg {ρ R : ℝ} (χ : Space → ℝ)
    (hρ : 0 ≤ ρ) (hχ : ∀ x, 0 ≤ χ x) (x : Space) : 0 ≤ smooth ρ R χ x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (hχ y) (sharp_nonneg hρ _)

theorem smooth_le {ρ R : ℝ} (χ : Space → ℝ)
    (hρ : 0 ≤ ρ) (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ)
    (hmass : ∫ x, χ x = 1) (x : Space) : smooth ρ R χ x ≤ ρ := by
  have hbound := convolution_mono_right_of_nonneg
    (f := χ) (g := sharp ρ R) (g' := fun _ => ρ)
    (x := x) (hiχ.mul_const ρ) hχ (sharp_le hρ) (fun _ => hρ)
  simpa only [smooth, convolution_def, lsmul_apply, smul_eq_mul,
    integral_mul_const, hmass, one_mul] using hbound

theorem smooth_integrable (ρ R : ℝ) (χ : Space → ℝ) (hiχ : Integrable χ) :
    Integrable (smooth ρ R χ) :=
  hiχ.integrable_convolution (L := lsmul ℝ ℝ) (sharp_integrable ρ R)

theorem smooth_mass (ρ : ℝ) {R : ℝ} (hR : 0 ≤ R) (χ : Space → ℝ)
    (hiχ : Integrable χ) (hmass : ∫ x, χ x = 1) :
    ∫ x, smooth ρ R χ x = ρ * R ^ 3 := by
  rw [smooth, integral_convolution (lsmul ℝ ℝ) hiχ (sharp_integrable ρ R), hmass]
  simpa using sharp_mass ρ hR

theorem smooth_support {ρ R a : ℝ} (χ : Space → ℝ)
    (hsupp : Function.support χ ⊆ closedBall 0 a) :
    Function.support (smooth ρ R χ) ⊆ cube (R + 2 * a) := by
  intro x hx
  obtain ⟨u, hu, v, hv, huv⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
  have hu' : ‖u‖ ≤ a := by simpa only [mem_closedBall, dist_zero_right] using hsupp hu
  have hv' := sharp_support ρ R hv
  rw [← huv]
  intro k
  have huk : |u k| ≤ a := by
    have hk : |u k| ≤ ‖u‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u k
    exact hk.trans hu'
  have hadd := abs_add_le (u k) (v k)
  change |u k + v k| < (R + 2 * a) / 2
  linarith [hv' k]

theorem smooth_compact {ρ R a : ℝ} (χ : Space → ℝ)
    (hsupp : Function.support χ ⊆ closedBall 0 a) : HasCompactSupport (smooth ρ R χ) :=
  compactSupport_of_cube_support (smooth_support χ hsupp)

theorem smooth_plateau {ρ R a : ℝ} (χ : Space → ℝ)
    (hmass : ∫ x, χ x = 1) (hsupp : Function.support χ ⊆ closedBall 0 a)
    {x : Space} (hx : x ∈ cube (R - 2 * a)) : smooth ρ R χ x = ρ := by
  have heq (y : Space) : χ y * sharp ρ R (x - y) = χ y * ρ := by
    by_cases hy : χ y = 0
    · simp [hy]
    · have hnorm : ‖y‖ ≤ a := by
        simpa only [mem_closedBall, dist_zero_right] using hsupp hy
      have hdist : x - y ∈ closedBall x a := by
        simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hnorm
      have hinside := closedBall_subset_cube hx hdist
      simp only [sharp, indicator_of_mem hinside]
  simp only [smooth, convolution_def, lsmul_apply, smul_eq_mul, heq,
    integral_mul_const, hmass, one_mul]

/-- The Fisher density vanishes both on the plateau and outside the outer
cube. These are global extrema of the nonnegative square root, so the claim
also holds at nondifferentiable points under mathlib's derivative convention. -/
theorem fisher_support {ρ R a : ℝ} (χ : Space → ℝ)
    (hρ : 0 ≤ ρ) (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ)
    (hmass : ∫ x, χ x = 1) (hsupp : Function.support χ ⊆ closedBall 0 a) :
    Function.support (fisherDensity (smooth ρ R χ)) ⊆
      cube (R + 2 * a) \ cube (R - 2 * a) := by
  intro x hx
  have houter : x ∈ cube (R + 2 * a) := by
    by_contra hnot
    have hz : smooth ρ R χ x = 0 := by
      by_contra hne
      exact hnot (smooth_support χ hsupp hne)
    have hmin : IsLocalMin (fun y => Real.sqrt (smooth ρ R χ y)) x := by
      apply Filter.Eventually.of_forall
      intro y
      simpa only [hz, Real.sqrt_zero] using Real.sqrt_nonneg (smooth ρ R χ y)
    exact hx (by simp [fisherDensity, hmin.fderiv_eq_zero])
  refine ⟨houter, ?_⟩
  intro hinner
  have hp := smooth_plateau (ρ := ρ) χ hmass hsupp hinner
  have hmax : IsLocalMax (fun y => Real.sqrt (smooth ρ R χ y)) x := by
    apply Filter.Eventually.of_forall
    intro y
    change Real.sqrt (smooth ρ R χ y) ≤ Real.sqrt (smooth ρ R χ x)
    rw [hp]
    exact Real.sqrt_le_sqrt (smooth_le χ hρ hχ hiχ hmass y)
  exact hx (by simp [fisherDensity, hmax.fderiv_eq_zero])

/-- The general convolution Sobolev theorem, independent of any region or
surface estimate. It combines the standard square-root regularity statement
with the pointwise Hoffmann--Ostenhof inequality and its Dirichlet integral. -/
structure ConvolutionSobolevLaws (H1 : Submodule ℝ (Space → ℝ))
    (energy : (Space → ℝ) → ℝ) : Prop where
  convolution : ∀ (χ g : Space → ℝ) (M : ℝ), 0 ≤ M →
    (∀ x, 0 ≤ g x ∧ g x ≤ M) → Integrable g →
    (∀ x, 0 ≤ χ x) → Integrable χ → (∫ x, χ x) = 1 →
    (fun x => Real.sqrt (χ x)) ∈ H1 → ContDiff ℝ ∞ (fun x => Real.sqrt (χ x)) →
    Integrable (fisherDensity χ) →
    let β := χ ⋆[lsmul ℝ ℝ] g
    (fun x => Real.sqrt (β x)) ∈ H1 ∧ Integrable (fisherDensity β) ∧
      energy (fun x => Real.sqrt (β x)) = ∫ x, fisherDensity β x ∧
      (∀ x, fisherDensity β x ≤ M * ∫ y, fisherDensity χ y)

/-- The surface estimate is derived from convolution regularity, actual
vanishing of the Fisher density off the transition shell, and the cubic
shell volume. No final background-energy bound is a hypothesis. -/
theorem smooth_fisher_surface_bound
    (H1 : Submodule ℝ (Space → ℝ)) (energy : (Space → ℝ) → ℝ)
    (laws : ConvolutionSobolevLaws H1 energy) {ρ R a : ℝ}
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hsize : 2 * a ≤ R) (χ : Space → ℝ)
    (hχ : ∀ x, 0 ≤ χ x) (hiχ : Integrable χ) (hmass : ∫ x, χ x = 1)
    (hsupp : Function.support χ ⊆ closedBall 0 a)
    (hroot : (fun x => Real.sqrt (χ x)) ∈ H1)
    (hrootSmooth : ContDiff ℝ ∞ (fun x => Real.sqrt (χ x)))
    (hfish : Integrable (fisherDensity χ)) :
    (fun x => Real.sqrt (smooth ρ R χ x)) ∈ H1 ∧
      energy (fun x => Real.sqrt (smooth ρ R χ x)) ≤
        16 * ρ * (∫ x, fisherDensity χ x) * R ^ 2 * a := by
  obtain ⟨hmem, hi, henergy, hpoint⟩ := laws.convolution χ (sharp ρ R) ρ hρ
    (fun x => ⟨sharp_nonneg hρ x, sharp_le hρ x⟩) (sharp_integrable ρ R)
    hχ hiχ hmass hroot hrootSmooth hfish
  refine ⟨hmem, ?_⟩
  change Integrable (fisherDensity (smooth ρ R χ)) at hi
  change (∀ x, fisherDensity (smooth ρ R χ) x ≤ ρ * ∫ y, fisherDensity χ y) at hpoint
  change energy (fun x => Real.sqrt (smooth ρ R χ x)) =
    ∫ x, fisherDensity (smooth ρ R χ) x at henergy
  rw [henergy]
  let W := cube (R + 2 * a) \ cube (R - 2 * a)
  have hWmeas : MeasurableSet W := (measurableSet_cube _).diff (measurableSet_cube _)
  have hWfin : volume W ≠ ⊤ := ne_top_of_le_ne_top (volume_cube_ne_top _) (measure_mono Set.sdiff_subset)
  have hbound : (∫ x, fisherDensity (smooth ρ R χ) x) ≤
      (ρ * ∫ y, fisherDensity χ y) * volume.real W := by
    calc
      _ ≤ ∫ x, W.indicator (fun _ => ρ * ∫ y, fisherDensity χ y) x := by
        apply integral_mono hi ((integrableOn_const hWfin).integrable_indicator hWmeas)
        intro x
        by_cases hx : x ∈ W
        · simpa only [indicator_of_mem hx] using hpoint x
        · have hz : fisherDensity (smooth ρ R χ) x = 0 := by
            by_contra hne
            exact hx (fisher_support χ hρ hχ hiχ hmass hsupp hne)
          simp only [hz, indicator_of_notMem hx, le_refl]
      _ = _ := by rw [integral_indicator hWmeas, setIntegral_const]; simp only [smul_eq_mul]; ring
  have hnonneg : 0 ≤ ρ * ∫ y, fisherDensity χ y :=
    mul_nonneg hρ (integral_nonneg fun y => sq_nonneg _)
  have hvolume := mul_le_mul_of_nonneg_left (volume_cube_shell_le ha hsize) hnonneg
  calc
    _ ≤ (ρ * ∫ y, fisherDensity χ y) * volume.real W := hbound
    _ ≤ (ρ * ∫ y, fisherDensity χ y) * (16 * R ^ 2 * a) := hvolume
    _ = _ := by ring

end Jellium.SmoothCube
