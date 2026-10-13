import Jellium.Collar
import Jellium.Upper
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Actual smooth cutoff functions for the compensated collar.  The cutoff and
bump are constructed from mathlib's smooth transition and smooth bump.
-/

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace Jellium.SmoothCollar

noncomputable def cutoff (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

noncomputable def outerBump : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

noncomputable def bump (t : ℝ) : ℝ := outerBump t

theorem cutoff_nonneg (t : ℝ) : 0 ≤ cutoff t := Real.smoothTransition.nonneg _
theorem cutoff_le_one (t : ℝ) : cutoff t ≤ 1 := Real.smoothTransition.le_one _

theorem cutoff_zero {t : ℝ} (ht : t ≤ 1 / 4) : cutoff t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem cutoff_one {t : ℝ} (ht : 3 / 4 ≤ t) : cutoff t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  exact Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id |>.sub contDiff_const)

theorem bump_nonneg (t : ℝ) : 0 ≤ bump t := outerBump.nonneg
theorem bump_le_one (t : ℝ) : bump t ≤ 1 := outerBump.le_one
theorem bump_smooth : ContDiff ℝ ∞ bump := outerBump.contDiff

theorem bump_zero_left {t : ℝ} (ht : t ≤ 5 / 4) : bump t = 0 := by
  apply outerBump.zero_of_le_dist
  change (1 / 4 : ℝ) ≤ dist t (3 / 2)
  rw [Real.dist_eq]
  have : t - 3 / 2 ≤ 0 := by linarith
  rw [abs_of_nonpos this]
  linarith

theorem bump_zero_right {t : ℝ} (ht : 7 / 4 ≤ t) : bump t = 0 := by
  apply outerBump.zero_of_le_dist
  change (1 / 4 : ℝ) ≤ dist t (3 / 2)
  rw [Real.dist_eq, abs_of_nonneg (show 0 ≤ t - 3 / 2 by linarith)]
  linarith

theorem bump_one {t : ℝ} (ht : t ∈ Icc (11 / 8) (13 / 8)) : bump t = 1 := by
  apply outerBump.one_of_mem_closedBall
  change dist t (3 / 2) ≤ (1 / 8 : ℝ)
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [ht.1, ht.2]

theorem bump_support : Function.support bump ⊆ Icc (1 : ℝ) 2 := by
  intro t ht
  change bump t ≠ 0 at ht
  constructor
  · by_contra h
    exact ht (bump_zero_left (by linarith))
  · by_contra h
    exact ht (bump_zero_right (by linarith))

theorem bump_integrable : IntegrableOn bump (Icc (1 : ℝ) 2) :=
  bump_smooth.continuous.continuousOn.integrableOn_Icc

noncomputable def bumpMass : ℝ := ∫ t in Icc (1 : ℝ) 2, bump t

theorem bumpMass_pos : 0 < bumpMass := by
  have hsmall : Icc (11 / 8 : ℝ) (13 / 8) ⊆ Icc (1 : ℝ) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hlower : (1 / 4 : ℝ) ≤ bumpMass := by
    have hmono := setIntegral_mono_set bump_integrable
      (Filter.Eventually.of_forall (fun t => bump_nonneg t)) (ae_of_all _ hsmall)
    change (∫ t in Icc (11 / 8 : ℝ) (13 / 8), bump t) ≤ bumpMass at hmono
    have heq : (∫ t in Icc (11 / 8 : ℝ) (13 / 8), bump t) = 1 / 4 := by
      rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => bump_one ht)]
      norm_num [setIntegral_const, Real.volume_Icc, measureReal_def]
    rwa [heq] at hmono
  linarith

noncomputable def weight (r a t : ℝ) : ℝ := (r + a * t) ^ 2

theorem weight_nonneg (r a t : ℝ) : 0 ≤ weight r a t := sq_nonneg _

theorem weight_lower {r a t : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    r ^ 2 ≤ weight r a t := by
  unfold weight
  nlinarith [mul_nonneg ha ht]

theorem weight_upper {r a t : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (har : 2 * a ≤ r) (ht : t ∈ Icc (0 : ℝ) 2) :
    weight r a t ≤ 4 * r ^ 2 := by
  have hlow : 0 ≤ r + a * t := add_nonneg hr (mul_nonneg ha ht.1)
  have hu : r + a * t ≤ 2 * r := by nlinarith [ht.2]
  unfold weight
  nlinarith

theorem missing_integrable (r a : ℝ) :
    IntegrableOn (fun t => (1 - cutoff t ^ 2) * weight r a t) (Icc 0 2) := by
  apply ContinuousOn.integrableOn_Icc
  exact ((continuous_const.sub (cutoff_smooth.continuous.pow 2)).mul
    ((continuous_const.add (continuous_const.mul continuous_id)).pow 2)).continuousOn

theorem profile_integrable (r a : ℝ) :
    IntegrableOn (fun t => bump t * weight r a t) (Icc 0 2) := by
  apply ContinuousOn.integrableOn_Icc
  exact (bump_smooth.continuous.mul
    ((continuous_const.add (continuous_const.mul continuous_id)).pow 2)).continuousOn

theorem missing_nonneg (r a t : ℝ) :
    0 ≤ (1 - cutoff t ^ 2) * weight r a t := by
  apply mul_nonneg _ (weight_nonneg _ _ _)
  nlinarith [cutoff_nonneg t, cutoff_le_one t]

theorem missing_bounds {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) :
    r ^ 2 / 4 ≤ Collar.missingMass cutoff (weight r a) ∧
      Collar.missingMass cutoff (weight r a) ≤ 9 * r ^ 2 / 4 := by
  have hsub : Icc (0 : ℝ) (1 / 4) ⊆ Icc 0 2 := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hsub1 : Icc (0 : ℝ) 1 ⊆ Icc 0 2 := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hsmall := (missing_integrable r a).mono_set hsub
  have hmid := (missing_integrable r a).mono_set hsub1
  constructor
  · have hmono := setIntegral_mono_set (missing_integrable r a)
      (ae_of_all _ (missing_nonneg r a)) (ae_of_all _ hsub)
    have hpoint := setIntegral_mono_on
      (show IntegrableOn (fun _ : ℝ => r ^ 2) (Icc 0 (1 / 4)) from
        continuous_const.continuousOn.integrableOn_Icc)
      hsmall measurableSet_Icc (fun t ht => show r ^ 2 ≤ (1 - cutoff t ^ 2) * weight r a t by
        rw [cutoff_zero ht.2]
        simpa using weight_lower hr.le ha ht.1)
    have heval : (∫ _t in Icc (0 : ℝ) (1 / 4), r ^ 2) = r ^ 2 / 4 := by
      norm_num [setIntegral_const, measureReal_def, Real.volume_Icc]
      ring
    rw [heval] at hpoint
    exact le_trans hpoint hmono
  · have hrestrict : Collar.missingMass cutoff (weight r a) =
        ∫ t in Icc (0 : ℝ) 1, (1 - cutoff t ^ 2) * weight r a t := by
      unfold Collar.missingMass
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub1
      intro t ht
      have ht1 : 1 < t := by
        by_contra h
        exact ht.2 ⟨ht.1.1, le_of_not_gt h⟩
      rw [cutoff_one (by linarith)]
      ring
    rw [hrestrict]
    have hpoint := setIntegral_mono_on hmid
      (show IntegrableOn (fun _ : ℝ => 9 * r ^ 2 / 4) (Icc 0 1) from
        continuous_const.continuousOn.integrableOn_Icc)
      measurableSet_Icc (fun t ht => show
        (1 - cutoff t ^ 2) * weight r a t ≤ 9 * r ^ 2 / 4 by
        have hw : weight r a t ≤ 9 * r ^ 2 / 4 := by
          have hlow : 0 ≤ r + a * t := add_nonneg hr.le (mul_nonneg ha ht.1)
          have hu : r + a * t ≤ 3 * r / 2 := by nlinarith [ht.2]
          unfold weight
          nlinarith
        have hmul := mul_nonneg (sq_nonneg (cutoff t)) (weight_nonneg r a t)
        nlinarith)
    simpa [setIntegral_const, measureReal_def, Real.volume_Icc] using hpoint

theorem profile_bounds {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) :
    r ^ 2 * bumpMass ≤ Collar.profileMass bump (weight r a) ∧
      Collar.profileMass bump (weight r a) ≤ 4 * r ^ 2 * bumpMass := by
  rw [Collar.profile_mass_outer_interval bump (weight r a) bump_support]
  have hsub : Icc (1 : ℝ) 2 ⊆ Icc (0 : ℝ) 2 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hint := (profile_integrable r a).mono_set hsub
  constructor
  · have h := setIntegral_mono_on (bump_integrable.const_mul (r ^ 2)) hint
      measurableSet_Icc (fun t ht => show r ^ 2 * bump t ≤ bump t * weight r a t by
        have := mul_le_mul_of_nonneg_left (weight_lower (t := t) hr.le ha (by linarith [ht.1]))
          (bump_nonneg t)
        nlinarith)
    simpa [integral_const_mul, bumpMass] using h
  · have h := setIntegral_mono_on hint (bump_integrable.const_mul (4 * r ^ 2))
      measurableSet_Icc (fun t ht => show bump t * weight r a t ≤ 4 * r ^ 2 * bump t by
        have := mul_le_mul_of_nonneg_left (weight_upper hr.le ha har (hsub ht))
          (bump_nonneg t)
        nlinarith)
    simpa [integral_const_mul, bumpMass] using h

theorem coefficient_bounds {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) :
    1 / (16 * bumpMass) ≤ Collar.coefficient cutoff bump (weight r a) ∧
      Collar.coefficient cutoff bump (weight r a) ≤ 9 / (4 * bumpMass) := by
  exact Upper.collar_coefficient_bounds hr bumpMass_pos
    (missing_bounds hr ha har).1 (missing_bounds hr ha har).2
    (profile_bounds hr ha har).1 (profile_bounds hr ha har).2

theorem coefficient_nonneg {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) :
    0 ≤ Collar.coefficient cutoff bump (weight r a) := by
  have hb := bumpMass_pos
  exact le_trans (by positivity) (coefficient_bounds hr ha har).1

theorem correction_neutral {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) :
    (∫ t in Icc (0 : ℝ) 2,
      (Collar.correctedProfile cutoff bump (weight r a) t - 1) * weight r a t) = 0 := by
  apply Collar.corrected_profile_neutral cutoff bump (weight r a)
    (missing_integrable r a) (profile_integrable r a)
  exact ne_of_gt (lt_of_lt_of_le (mul_pos (sq_pos_of_pos hr) bumpMass_pos)
    (profile_bounds hr ha har).1)

noncomputable def rootProfile (c t : ℝ) : ℝ := Real.sqrt (cutoff t ^ 2 + c * bump t)

theorem rootProfile_nonneg (c t : ℝ) : 0 ≤ rootProfile c t := Real.sqrt_nonneg _

theorem rootProfile_eq_cutoff {c t : ℝ} (ht : t ≤ 5 / 4) : rootProfile c t = cutoff t := by
  unfold rootProfile
  rw [bump_zero_left ht]
  simpa using Real.sqrt_sq (cutoff_nonneg t)

theorem rootProfile_eq_outer {c t : ℝ} (ht : 3 / 4 ≤ t) :
    rootProfile c t = Real.sqrt (1 + c * bump t) := by
  unfold rootProfile
  rw [cutoff_one ht]
  norm_num

theorem rootProfile_smooth {c : ℝ} (hc : 0 ≤ c) : ContDiff ℝ ∞ (rootProfile c) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < 5 / 4
  · apply cutoff_smooth.contDiffAt.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact rootProfile_eq_cutoff (le_of_lt hx)
  · have hcut : cutoff t = 1 := cutoff_one (by linarith)
    apply ((cutoff_smooth.pow 2).add (contDiff_const.mul bump_smooth)).contDiffAt.sqrt
    rw [hcut]
    have := mul_nonneg hc (bump_nonneg t)
    positivity

theorem rootProfile_zero {c t : ℝ} (ht : t ≤ 1 / 4) : rootProfile c t = 0 := by
  rw [rootProfile_eq_cutoff (by linarith), cutoff_zero ht]

theorem rootProfile_one {c t : ℝ} (ht : 7 / 4 ≤ t) : rootProfile c t = 1 := by
  rw [rootProfile_eq_outer (by linarith), bump_zero_right ht]
  norm_num

theorem rootProfile_sq {c t : ℝ} (hc : 0 ≤ c) :
    rootProfile c t ^ 2 = cutoff t ^ 2 + c * bump t := by
  apply Real.sq_sqrt
  exact add_nonneg (sq_nonneg _) (mul_nonneg hc (bump_nonneg _))

theorem rootProfile_sq_bound {c C t : ℝ} (hc : 0 ≤ c) (hC : c ≤ C) :
    rootProfile c t ^ 2 ≤ 1 + C := by
  rw [rootProfile_sq hc]
  have hmul := mul_le_mul_of_nonneg_left (bump_le_one t) hc
  nlinarith [cutoff_nonneg t, cutoff_le_one t]

theorem rootProfile_deriv_left {c t : ℝ} (ht : t < 5 / 4) :
    deriv (rootProfile c) t = deriv cutoff t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Iio_mem_nhds ht] with x hx
  exact rootProfile_eq_cutoff (le_of_lt hx)

theorem rootProfile_deriv_right {c t : ℝ} (hc : 0 ≤ c) (ht : 3 / 4 < t) :
    deriv (rootProfile c) t = c * deriv bump t / (2 * Real.sqrt (1 + c * bump t)) := by
  have heq : rootProfile c =ᶠ[𝓝 t] (fun x => Real.sqrt (1 + c * bump x)) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact rootProfile_eq_outer (le_of_lt hx)
  rw [heq.deriv_eq]
  have hb : HasDerivAt bump (deriv bump t) t :=
    (bump_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hf := (hb.const_mul c).const_add 1
  have hpos : 0 < 1 + c * bump t := by
    have := mul_nonneg hc (bump_nonneg t)
    linarith
  simpa using (hf.sqrt (ne_of_gt hpos)).deriv

theorem exists_uniform_derivative_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : ℝ, 0 ≤ c → c ≤ 9 / (4 * bumpMass) →
      ∀ t ∈ Icc (0 : ℝ) 2, |deriv (rootProfile c) t| ≤ B := by
  obtain ⟨S, hS⟩ := isCompact_Icc.bddAbove_image
    ((cutoff_smooth.continuous_deriv (by simp)).abs.continuousOn :
      ContinuousOn (fun t => |deriv cutoff t|) (Icc (0 : ℝ) 2))
  obtain ⟨P, hP⟩ := isCompact_Icc.bddAbove_image
    ((bump_smooth.continuous_deriv (by simp)).abs.continuousOn :
      ContinuousOn (fun t => |deriv bump t|) (Icc (0 : ℝ) 2))
  have hSpos : 0 ≤ S := le_trans (abs_nonneg _) (hS ⟨0, by norm_num, rfl⟩)
  have hPpos : 0 ≤ P := le_trans (abs_nonneg _) (hP ⟨0, by norm_num, rfl⟩)
  let C := 9 / (4 * bumpMass)
  have hCpos : 0 ≤ C := by
    have hb := bumpMass_pos
    dsimp [C]
    positivity
  refine ⟨S + C * P, add_nonneg hSpos (mul_nonneg hCpos hPpos), ?_⟩
  intro c hc hcC t ht
  by_cases hleft : t < 5 / 4
  · rw [rootProfile_deriv_left hleft]
    exact le_trans (hS ⟨t, ht, rfl⟩) (le_add_of_nonneg_right (mul_nonneg hCpos hPpos))
  · rw [rootProfile_deriv_right hc (by linarith)]
    have hroot : 1 ≤ Real.sqrt (1 + c * bump t) := by
      apply (Real.one_le_sqrt).2
      exact le_add_of_nonneg_right (mul_nonneg hc (bump_nonneg t))
    rw [abs_div, abs_mul, abs_of_nonneg hc,
      abs_of_nonneg (show 0 ≤ 2 * Real.sqrt (1 + c * bump t) by positivity)]
    apply (div_le_iff₀ (show 0 < 2 * Real.sqrt (1 + c * bump t) by linarith)).2
    have hderiv := hP ⟨t, ht, rfl⟩
    have hmul := mul_le_mul hcC hderiv (abs_nonneg _) hCpos
    have hprod := mul_le_mul_of_nonneg_left (show 1 ≤ 2 * Real.sqrt (1 + c * bump t) by linarith)
      (show 0 ≤ S + C * P by positivity)
    nlinarith

theorem exists_uniform_gradient_integral :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 ≤ c → c ≤ 9 / (4 * bumpMass) →
      (∫ t in Icc (0 : ℝ) 2, (deriv (rootProfile c) t) ^ 2) ≤ K := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_derivative_bound
  refine ⟨2 * B ^ 2, by positivity, ?_⟩
  intro c hc hcC
  have hint : IntegrableOn (fun t => deriv (rootProfile c) t ^ 2) (Icc 0 2) :=
    (((rootProfile_smooth hc).continuous_deriv (by simp)).pow 2).continuousOn.integrableOn_Icc
  have hconst : IntegrableOn (fun _t : ℝ => B ^ 2) (Icc 0 2) :=
    continuous_const.continuousOn.integrableOn_Icc
  have h := setIntegral_mono_on hint hconst measurableSet_Icc (fun t ht => by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (deriv (rootProfile c) t)) hB).2 (hbound c hc hcC t ht))
  simpa [setIntegral_const, measureReal_def, Real.volume_Icc] using h

end Jellium.SmoothCollar
