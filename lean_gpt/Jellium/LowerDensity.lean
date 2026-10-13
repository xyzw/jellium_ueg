import Jellium.Scales
import Jellium.SmoothingError
import Jellium.CoulombError
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual lower-comparison density sequence. A standard compact mollifier is
the sole function chosen as input. Every density, smoothing scale and support
margin in the construction is defined below. -/

open Set Metric MeasureTheory Filter Topology
open scoped ContDiff

namespace Jellium.LowerDensity

open Contraction

structure Mollifier (A : ℝ) where
  value : Space → ℝ
  continuous : Continuous value
  sqrt_smooth : ContDiff ℝ ∞ (fun x => Real.sqrt (value x))
  nonnegative : ∀ x, 0 ≤ value x
  integral_one : (∫ x, value x) = 1
  support : Function.support value ⊆ ball 0 A

variable {A : ℝ} (χ : Mollifier A)

theorem Mollifier.compact : HasCompactSupport χ.value := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) A)
  intro x hx
  by_contra hnonzero
  exact hx (ball_subset_closedBall (χ.support hnonzero))

theorem Mollifier.integrable : Integrable χ.value :=
  χ.continuous.integrable_of_hasCompactSupport χ.compact

noncomputable def scaledKernel (d : ℝ) : Space → ℝ := contract d χ.value

theorem scaledKernel_nonneg {d : ℝ} (hd : 0 < d) (x : Space) :
    0 ≤ scaledKernel χ d x := mul_nonneg (by positivity) (χ.nonnegative _)

theorem scaledKernel_mass {d : ℝ} (hd : 0 < d) : (∫ x, scaledKernel χ d x) = 1 := by
  rw [scaledKernel, contract_mass hd, χ.integral_one]

theorem scaledKernel_integrable {d : ℝ} (hd : 0 < d) : Integrable (scaledKernel χ d) :=
  contract_integrable hd χ.integrable

theorem scaledKernel_support {d : ℝ} (hd : 0 < d) :
    Function.support (scaledKernel χ d) ⊆ closedBall 0 (A * d) := by
  change Function.support (contract d χ.value) ⊆ closedBall 0 (A * d)
  have h := contract_support hd χ.value χ.support
  simpa only [mul_comm d A] using Set.Subset.trans h ball_subset_closedBall

theorem scaledKernel_continuous (d : ℝ) : Continuous (scaledKernel χ d) := by
  change Continuous (fun x => d⁻¹ ^ 3 * χ.value (d⁻¹ • x))
  exact continuous_const.mul (χ.continuous.comp (continuous_id.const_smul d⁻¹))

theorem scaledKernel_compact {d : ℝ} (hd : 0 < d) : HasCompactSupport (scaledKernel χ d) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (A * d))
  intro x hx
  by_contra hnonzero
  exact hx (scaledKernel_support χ hd hnonzero)

theorem scaledKernel_firstMoment_integrable {d : ℝ} (hd : 0 < d) :
    Integrable (fun x => scaledKernel χ d x * ‖x‖) :=
  ((scaledKernel_continuous χ d).mul continuous_norm).integrable_of_hasCompactSupport
    ((scaledKernel_compact χ hd).mul_right)

noncomputable def smoothingScale (b A : ℝ) (n : ℕ) : ℝ :=
  Scales.width n / Scales.safeFactor b A n

noncomputable def preDensity (ρ b : ℝ) (n : ℕ) : Space → ℝ :=
  smoothBall ρ (Scales.radius b n) (scaledKernel χ (smoothingScale b A n))

noncomputable def density (ρ b : ℝ) (n : ℕ) : Space → ℝ :=
  contract (Scales.safeFactor b A n) (preDensity χ ρ b n)

noncomputable def background (ρ b : ℝ) (n : ℕ) : Space → ℝ :=
  sharpBall ρ (Scales.radius b n)

theorem smoothingScale_pos (b : ℝ) (n : ℕ) : 0 < smoothingScale b A n := by
  have hs := Scales.size_pos n
  exact div_pos (inv_pos.mpr hs) (Scales.safeFactor_pos b A n)

theorem preDensity_bounds {ρ : ℝ} (hρ : 0 ≤ ρ) (b : ℝ) (n : ℕ) (x : Space) :
    0 ≤ preDensity χ ρ b n x ∧ preDensity χ ρ b n x ≤ ρ := by
  have hd := smoothingScale_pos (A := A) b n
  exact ⟨smoothBall_nonneg _ hρ (scaledKernel_nonneg χ hd) x,
    smoothBall_le _ hρ (scaledKernel_nonneg χ hd) (scaledKernel_integrable χ hd)
      (scaledKernel_mass χ hd) x⟩

theorem preDensity_integrable (ρ b : ℝ) (n : ℕ) : Integrable (preDensity χ ρ b n) :=
  (scaledKernel_integrable χ (smoothingScale_pos b n)).integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (sharpBall_integrable _ _)

theorem density_integrable (ρ b : ℝ) (n : ℕ) : Integrable (density χ ρ b n) :=
  contract_integrable (Scales.safeFactor_pos b A n) (preDensity_integrable χ ρ b n)

theorem density_bounds {ρ : ℝ} (hρ : 0 ≤ ρ) (b : ℝ) (n : ℕ) (x : Space) :
    0 ≤ density χ ρ b n x ∧ density χ ρ b n x ≤ 8 * ρ :=
  contract_bounds (Scales.safeFactor_half b A n) hρ _ (preDensity_bounds χ hρ b n) x

theorem preDensity_mass (ρ b : ℝ) (n : ℕ) :
    (∫ x, preDensity χ ρ b n x) =
      ρ * (volume (ball (0 : Space) (Scales.radius b n))).toReal :=
  smoothBall_mass _ _ _ (scaledKernel_integrable χ (smoothingScale_pos b n))
    (scaledKernel_mass χ (smoothingScale_pos b n))

theorem density_mass (ρ b : ℝ) (n : ℕ) :
    (∫ x, density χ ρ b n x) =
      ρ * (volume (ball (0 : Space) (Scales.radius b n))).toReal := by
  rw [density, contract_mass (Scales.safeFactor_pos b A n), preDensity_mass]

theorem density_eventually_supported {ρ b : ℝ} (hb : 0 < b) (hA : 0 < A) :
    ∀ᶠ n in atTop, Function.support (density χ ρ b n) ⊆
      ball 0 (Scales.radius b n - A * Scales.width n) := by
  filter_upwards [Scales.safeFactor_eventually_eq hb hA] with n hn
  have hR : 0 < Scales.radius b n := by unfold Scales.radius; have hs := Scales.size_pos n; positivity
  apply contracted_smoothBall_support (Scales.safeFactor_pos b A n) (ne_of_gt hR)
    (hn.trans (Scales.factor_eq hb A n))
  have hsup := scaledKernel_support χ (smoothingScale_pos (A := A) b n)
  simpa only [smoothingScale, mul_div_assoc] using hsup

theorem density_l1_surface_bound {P ρ b : ℝ} (laws : BVEstimates P)
    (hP : 0 ≤ P) (hρ : 0 ≤ ρ) (hb : 0 < b) (hA : 0 < A) :
    ∀ᶠ n in atTop,
      (∫ x, |density χ ρ b n x - background ρ b n x|) ≤
        ((2 * P + 12 * (volume (ball (0 : Space) 1)).toReal) * ρ * A * b ^ 2) * Scales.size n ^ 3 := by
  filter_upwards [Scales.safeFactor_eventually_eq hb hA] with n hn
  have hs := Scales.size_pos n
  have hR : 0 < Scales.radius b n := by unfold Scales.radius; positivity
  have hd := smoothingScale_pos (A := A) b n
  have hsupport : Function.support (scaledKernel χ (smoothingScale b A n)) ⊆
      closedBall 0 (A * Scales.width n / Scales.safeFactor b A n) := by
    simpa only [smoothingScale, mul_div_assoc] using scaledKernel_support χ hd
  have h := contracted_smoothed_surface_error laws hP hρ hR hA.le (by exact (inv_pos.mpr hs).le)
    (Scales.safeFactor_half b A n) (Scales.safeFactor_le_one hb hA.le n)
    (hn.trans (Scales.factor_eq hb A n)) _ (scaledKernel_nonneg χ hd)
    (scaledKernel_integrable χ hd) (scaledKernel_firstMoment_integrable χ hd)
    (scaledKernel_mass χ hd) hsupport
  change (∫ x, |density χ ρ b n x - background ρ b n x|) ≤ _ at h
  convert h using 1
  unfold Scales.radius Scales.width
  field_simp

theorem density_difference_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (b : ℝ) (n : ℕ) (x : Space) :
    |density χ ρ b n x - background ρ b n x| ≤ 8 * ρ := by
  have hd := smoothingScale_pos (A := A) b n
  exact contracted_difference_bound hρ (Scales.safeFactor_half b A n) _
    (scaledKernel_nonneg χ hd) (scaledKernel_integrable χ hd) (scaledKernel_mass χ hd) x



noncomputable def discrepancy (ρ b : ℝ) (n : ℕ) : Space → ℝ :=
  fun x => density χ ρ b n x - background ρ b n x

theorem discrepancy_integrable (ρ b : ℝ) (n : ℕ) : Integrable (discrepancy χ ρ b n) :=
  (density_integrable χ ρ b n).sub (sharpBall_integrable _ _)

theorem density_mass_integer {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (hunit : (volume (ball (0 : Space) 1)).toReal = κ) (n : ℕ) :
    (∫ x, density χ ρ (Scales.neutralScale ρ κ) n x) = (((n + 1) ^ 6 : ℕ) : ℝ) := by
  rw [density_mass]
  have hR : 0 ≤ Scales.radius (Scales.neutralScale ρ κ) n := by
    unfold Scales.radius
    exact mul_nonneg (Scales.neutralScale_pos hρ hκ).le (sq_nonneg _)
  have hvol := volume_ball_scale hR 1
  rw [mul_one, hunit] at hvol
  rw [hvol, mul_comm (Scales.radius (Scales.neutralScale ρ κ) n ^ 3) κ]
  exact Scales.neutral_radius hρ hκ n

theorem discrepancy_coulomb_tendsto_zero
    {energy : (Space → ℝ) → ℝ} {C P ρ b v : ℝ}
    (law : CoulombInterpolation energy C) (hC : 0 ≤ C)
    (bv : BVEstimates P) (hP : 0 ≤ P) (hρ : 0 ≤ ρ)
    (hb : 0 < b) (hA : 0 < A) (hv : 0 < v) :
    Tendsto (fun n => energy (discrepancy χ ρ b n) / (v * Scales.size n ^ 6))
      atTop (𝓝 0) := by
  let B := (2 * P + 12 * (volume (ball (0 : Space) 1)).toReal) * ρ * A * b ^ 2
  apply normalized_coulomb_tendsto_zero law hC (B := B) (L := 8 * ρ)
    (by dsimp [B]; positivity) (by positivity) hv Scales.size Scales.size_tendsto
      (discrepancy χ ρ b)
  filter_upwards [density_l1_surface_bound χ bv hP hρ hb hA] with n hn
  exact ⟨Scales.size_pos n, discrepancy_integrable χ ρ b n,
    density_difference_bound χ hρ b n, hn⟩

end Jellium.LowerDensity
