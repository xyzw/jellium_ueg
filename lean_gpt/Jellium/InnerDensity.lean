import Jellium.LowerDensity
import Jellium.Domains

/-! Smoothed inner balls for the direct lower comparison. The density is
bounded by the outer background, so its L¹ discrepancy is exactly the missing
mass. No density contraction, integer mean, or BV estimate is needed. -/

open Set Metric MeasureTheory Filter Topology

namespace Jellium.InnerDensity

open Contraction LowerDensity Domains

abbrev Space := Contraction.Space

noncomputable def innerRadius (n : ℕ) : ℝ := Scales.size n ^ 2
noncomputable def width (n : ℕ) : ℝ := (Scales.size n)⁻¹
noncomputable def outerRadius (A : ℝ) (n : ℕ) : ℝ :=
  innerRadius n + 2 * A * width n
noncomputable def density {A : ℝ} (χ : Mollifier A) (ρ : ℝ) (n : ℕ) : Space → ℝ :=
  smoothBall ρ (innerRadius n) (scaledKernel χ (width n))
noncomputable def discrepancy {A : ℝ} (χ : Mollifier A) (ρ : ℝ) (n : ℕ) : Space → ℝ :=
  fun x => density χ ρ n x - sharpBall ρ (outerRadius A n) x

theorem size_one_le (n : ℕ) : 1 ≤ Scales.size n := by
  dsimp [Scales.size]
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem innerRadius_pos (n : ℕ) : 0 < innerRadius n := sq_pos_of_pos (Scales.size_pos n)
theorem width_pos (n : ℕ) : 0 < width n := inv_pos.mpr (Scales.size_pos n)
theorem width_le_one (n : ℕ) : width n ≤ 1 := by
  exact inv_le_one_of_one_le₀ (size_one_le n)

theorem innerRadius_one_le (n : ℕ) : 1 ≤ innerRadius n := by
  dsimp [innerRadius]
  nlinarith [size_one_le n]

theorem inner_le_outer {A : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    innerRadius n ≤ outerRadius A n := by
  dsimp [outerRadius]
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hA) (width_pos n).le)

theorem outerRadius_one_le {A : ℝ} (hA : 0 ≤ A) (n : ℕ) : 1 ≤ outerRadius A n :=
  (innerRadius_one_le n).trans (inner_le_outer hA n)

theorem innerRadius_tendsto : Tendsto innerRadius atTop atTop :=
  (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Scales.size_tendsto

theorem outerRadius_tendsto {A : ℝ} (hA : 0 ≤ A) : Tendsto (outerRadius A) atTop atTop :=
  tendsto_atTop_mono (inner_le_outer hA) innerRadius_tendsto

theorem smoothing_ratio_tendsto :
    Tendsto (fun n => width n / innerRadius n) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp Scales.size_tendsto
  convert hi.pow 3 using 1
  · funext n
    dsimp [width, innerRadius]
    ring
  · norm_num

theorem smoothing_product_tendsto :
    Tendsto (fun n => width n * innerRadius n) atTop atTop := by
  convert Scales.size_tendsto using 1
  funext n
  dsimp [width, innerRadius]
  field_simp [ne_of_gt (Scales.size_pos n)]

theorem volume_ratio_tendsto (A : ℝ) :
    Tendsto (fun n => ballVolume (innerRadius n) / ballVolume (outerRadius A n))
      atTop (𝓝 1) := by
  have hratio : Tendsto (fun n => outerRadius A n / innerRadius n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add (smoothing_ratio_tendsto.const_mul (2 * A))
    convert h using 1
    · funext n
      dsimp [outerRadius]
      field_simp [ne_of_gt (innerRadius_pos n)]
    · norm_num
  have h := (hratio.pow 3).inv₀ (by norm_num : (1 : ℝ) ^ 3 ≠ 0)
  convert h using 1
  · funext n
    dsimp [ballVolume]
    field_simp
  · norm_num

theorem density_bounds {A ρ : ℝ} (χ : Mollifier A) (hρ : 0 ≤ ρ) (n : ℕ) (x : Space) :
    0 ≤ density χ ρ n x ∧ density χ ρ n x ≤ ρ :=
  ⟨smoothBall_nonneg _ hρ (scaledKernel_nonneg χ (width_pos n)) x,
    smoothBall_le _ hρ (scaledKernel_nonneg χ (width_pos n))
      (scaledKernel_integrable χ (width_pos n)) (scaledKernel_mass χ (width_pos n)) x⟩

theorem density_integrable {A : ℝ} (χ : Mollifier A) (ρ : ℝ) (n : ℕ) :
    Integrable (density χ ρ n) :=
  (scaledKernel_integrable χ (width_pos n)).integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (sharpBall_integrable _ _)

theorem density_mass {A : ℝ} (χ : Mollifier A) (ρ : ℝ) (n : ℕ) :
    (∫ x, density χ ρ n x) = ρ * ballVolume (innerRadius n) := by
  rw [density, smoothBall_mass _ _ _ (scaledKernel_integrable χ (width_pos n))
    (scaledKernel_mass χ (width_pos n))]
  exact congrArg (ρ * ·) (ball_volume_real (0 : Space) _ (innerRadius_pos n).le)

theorem density_support {A : ℝ} (χ : Mollifier A) (ρ : ℝ) (n : ℕ) :
    Function.support (density χ ρ n) ⊆ ball 0 (innerRadius n + A * width n) :=
  smoothBall_support _ (scaledKernel_support χ (width_pos n))

theorem density_le_background {A ρ : ℝ} (χ : Mollifier A) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (n : ℕ) (x : Space) : density χ ρ n x ≤ sharpBall ρ (outerRadius A n) x := by
  classical
  by_cases hx : x ∈ ball (0 : Space) (outerRadius A n)
  · simpa [sharpBall, hx] using (density_bounds χ hρ n x).2
  · have hz : density χ ρ n x = 0 := by
      by_contra h
      have hs := density_support χ ρ n h
      have hin : innerRadius n + A * width n ≤ outerRadius A n := by
        dsimp [outerRadius]
        have := mul_nonneg hA (width_pos n).le
        linarith
      exact hx (ball_subset_ball hin hs)
    simp [sharpBall, hx, hz]

theorem discrepancy_integrable {A : ℝ} (χ : Mollifier A) (ρ : ℝ) (n : ℕ) :
    Integrable (discrepancy χ ρ n) :=
  (density_integrable χ ρ n).sub (sharpBall_integrable _ _)

theorem discrepancy_bound {A ρ : ℝ} (χ : Mollifier A) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (n : ℕ) (x : Space) : |discrepancy χ ρ n x| ≤ ρ := by
  rw [discrepancy, abs_of_nonpos (sub_nonpos.mpr (density_le_background χ hA hρ n x))]
  have := sharpBall_le (R := outerRadius A n) hρ x
  have := (density_bounds χ hρ n x).1
  linarith

theorem discrepancy_l1 {A ρ : ℝ} (χ : Mollifier A) (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (n : ℕ) :
    (∫ x, |discrepancy χ ρ n x|) =
      ρ * (ballVolume (outerRadius A n) - ballVolume (innerRadius n)) := by
  have heq (x : Space) : |discrepancy χ ρ n x| =
      sharpBall ρ (outerRadius A n) x - density χ ρ n x := by
    rw [discrepancy, abs_of_nonpos (sub_nonpos.mpr (density_le_background χ hA hρ n x))]
    ring
  simp_rw [heq]
  rw [integral_sub (sharpBall_integrable _ _) (density_integrable χ ρ n),
    density_mass, sharpBall_mass]
  rw [show (volume (ball (0 : Space) (outerRadius A n))).toReal =
    ballVolume (outerRadius A n) from
      ball_volume_real _ _ (by linarith [outerRadius_one_le hA n])]
  ring

theorem radius_cube_difference_bound {A : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    outerRadius A n ^ 3 - innerRadius n ^ 3 ≤
      (6 * A + 12 * A ^ 2 + 8 * A ^ 3) * Scales.size n ^ 3 := by
  let t := Scales.size n
  have ht : 1 ≤ t := size_one_le n
  have ht0 : 0 < t := Scales.size_pos n
  have hi : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have hi1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have ht3 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have hi3 : t⁻¹ ^ 3 ≤ t ^ 3 := by
    have : t⁻¹ ^ 3 ≤ 1 := pow_le_one₀ hi hi1
    linarith
  have heq : outerRadius A n ^ 3 - innerRadius n ^ 3 =
      6 * A * t ^ 3 + 12 * A ^ 2 + 8 * A ^ 3 * t⁻¹ ^ 3 := by
    dsimp [outerRadius, innerRadius, width, t]
    field_simp [ne_of_gt (Scales.size_pos n)]
    ring
  rw [heq]
  have h1 := mul_le_mul_of_nonneg_left ht3 (show 0 ≤ 12 * A ^ 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hi3 (show 0 ≤ 8 * A ^ 3 by positivity)
  change _ ≤ (6 * A + 12 * A ^ 2 + 8 * A ^ 3) * t ^ 3
  nlinarith only [h1, h2]

theorem discrepancy_l1_bound {A ρ : ℝ} (χ : Mollifier A) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (n : ℕ) : (∫ x, |discrepancy χ ρ n x|) ≤
      (ρ * (Real.pi * 4 / 3) * (6 * A + 12 * A ^ 2 + 8 * A ^ 3)) * Scales.size n ^ 3 := by
  rw [discrepancy_l1 χ hA hρ]
  have h := mul_le_mul_of_nonneg_left (radius_cube_difference_bound hA n)
    (show 0 ≤ ρ * (Real.pi * 4 / 3) by positivity)
  dsimp [ballVolume]
  nlinarith only [h]

theorem discrepancy_coulomb_tendsto_zero
    {A ρ B : ℝ} (χ : Mollifier A) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    {energy : (Space → ℝ) → ℝ} (law : CoulombInterpolation energy B) (hB : 0 ≤ B) :
    Tendsto (fun n => energy (discrepancy χ ρ n) / ballVolume (innerRadius n))
      atTop (𝓝 0) := by
  have h := normalized_coulomb_tendsto_zero law hB
    (B := ρ * (Real.pi * 4 / 3) * (6 * A + 12 * A ^ 2 + 8 * A ^ 3)) (L := ρ)
    (by positivity) hρ (by positivity : 0 < Real.pi * 4 / 3)
    Scales.size Scales.size_tendsto (discrepancy χ ρ)
    (Eventually.of_forall fun n => ⟨Scales.size_pos n, discrepancy_integrable χ ρ n,
      discrepancy_bound χ hA hρ n, discrepancy_l1_bound χ hA hρ n⟩)
  convert h using 1
  funext n
  congr 1
  dsimp [ballVolume, innerRadius]
  ring

end Jellium.InnerDensity
