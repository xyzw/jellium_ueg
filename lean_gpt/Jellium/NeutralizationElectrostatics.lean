import Jellium.RadialShells
import Mathlib.MeasureTheory.Integral.Prod

/-! Radial shell cancellation for an arbitrary (not necessarily radial) core.
Newton's theorem identifies the core-shell interaction with the total core
charge times the constant potential inside the shell. The cancellation and
surface estimate below are proved directly from the radial Newton kernel. -/

open MeasureTheory Set

namespace Jellium.Neutralization

open RadialShells

/-- The radial Newton potential is constant throughout the core. No sign
condition on the shell charge is needed. -/
theorem potential_constant_inside (μ : ℝ → ℝ) (R W t : ℝ)
    (hR : 0 ≤ R) (ht : t ≤ R)
    (hs : ∀ s, s ∉ Icc R (R + W) → μ s = 0) :
    potential μ t = potential μ 0 := by
  unfold potential
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hmem : s ∈ Icc R (R + W)
  · rw [max_eq_right (ht.trans hmem.1), max_eq_right (hR.trans hmem.1)]
  · simp only [hs s hmem, zero_mul]

/-- An arbitrary core interacts with a radial shell only through its total
charge. The function recording the core radius can be the Euclidean norm,
and the core charge density is not required to be radial. -/
theorem core_shell_interaction {α : Type*} [MeasurableSpace α]
    (m : Measure α) (core : α → ℝ) (radius : α → ℝ) (μ : ℝ → ℝ) (R W : ℝ)
    (hR : 0 ≤ R)
    (hs : ∀ s, s ∉ Icc R (R + W) → μ s = 0)
    (hc : ∀ x, R < radius x → core x = 0) :
    (∫ x, core x * potential μ (radius x) ∂m) =
      (∫ x, core x ∂m) * potential μ 0 := by
  calc
    _ = ∫ x, core x * potential μ 0 ∂m := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : radius x ≤ R
      · rw [potential_constant_inside μ R W (radius x) hR hx hs]
      · simp only [hc x (lt_of_not_ge hx), zero_mul]
    _ = _ := integral_mul_const _ _

theorem shell_kernel_bound (R W s t : ℝ) (hR : 0 < R) (hW : 0 ≤ W)
    (hs : s ∈ Icc R (R + W)) (ht : t ≤ R + W) :
    |1 / max t s - 1 / R| ≤ W / R ^ 2 := by
  have hlow : R ≤ max t s := hs.1.trans (le_max_right _ _)
  have hupp : max t s ≤ R + W := max_le ht hs.2
  have hm : 0 < max t s := hR.trans_le hlow
  have hi := one_div_le_one_div_of_le hR hlow
  rw [abs_of_nonpos (sub_nonpos.mpr hi)]
  have heq : -(1 / max t s - 1 / R) = (max t s - R) / (R * max t s) := by
    field_simp
    ring
  rw [heq]
  apply div_le_div₀ hW (by linarith) (sq_pos_of_pos hR)
  nlinarith

theorem potential_abs_bound (μ : ℝ → ℝ) (R W t : ℝ) (hR : 0 < R)
    (hμ : Integrable μ) (hs : ∀ s, s ∉ Icc R (R + W) → μ s = 0) :
    |potential μ t| ≤ (1 / R) * ∫ s, |μ s| := by
  have h := norm_integral_le_of_norm_le (hμ.abs.const_mul (1 / R))
    (Filter.Eventually.of_forall (fun s : ℝ => show
      ‖μ s * (1 / max t s)‖ ≤ (1 / R) * |μ s| from by
      by_cases hh : s ∈ Icc R (R + W)
      · have hm : R ≤ max t s := hh.1.trans (le_max_right _ _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
          (one_div_nonneg.mpr (hR.le.trans hm))]
        nlinarith only [mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le hR hm) (abs_nonneg (μ s))]
      · simp [hs s hh]))
  simpa only [potential, Real.norm_eq_abs, integral_const_mul] using h

theorem radial_self_integrable (μ : ℝ → ℝ) (R W : ℝ) (hR : 0 < R)
    (hm : Measurable μ) (hμ : Integrable μ)
    (hs : ∀ s, s ∉ Icc R (R + W) → μ s = 0) :
    Integrable (fun t => μ t * potential μ t) := by
  have hp : StronglyMeasurable (potential μ) := by
    have hf : Measurable (fun z : ℝ × ℝ => μ z.2 * (1 / max z.1 z.2)) :=
      (hm.comp measurable_snd).mul (measurable_const.div (measurable_fst.max measurable_snd))
    exact hf.stronglyMeasurable.integral_prod_right' 
  apply (hμ.abs.const_mul ((1 / R) * ∫ s, |μ s|)).mono'
    (hμ.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards [] with t
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  nlinarith only [mul_le_mul_of_nonneg_left
    (potential_abs_bound μ R W t hR hμ hs) (abs_nonneg (μ t))]

theorem potential_remainder_bound (μ : ℝ → ℝ) (R W Q t : ℝ)
    (hR : 0 < R) (hW : 0 ≤ W) (ht : t ≤ R + W)
    (hμ : Integrable μ) (hs : ∀ s, s ∉ Icc R (R + W) → μ s = 0)
    (hmass : ∫ s, μ s = -Q) :
    |potential μ t + Q / R| ≤ (W / R ^ 2) * ∫ s, |μ s| := by
  have hid : potential μ t + Q / R =
      ∫ s, μ s * (1 / max t s - 1 / R) := by
    simp_rw [mul_sub]
    rw [integral_sub (potential_integrable μ R W t hR hμ hs)
      (hμ.mul_const (1 / R)), integral_mul_const, hmass]
    unfold potential
    ring
  rw [hid]
  have h := norm_integral_le_of_norm_le (hμ.abs.const_mul (W / R ^ 2))
    (Filter.Eventually.of_forall (fun s : ℝ => show
      ‖μ s * (1 / max t s - 1 / R)‖ ≤ (W / R ^ 2) * |μ s| from by
      by_cases hh : s ∈ Icc R (R + W)
      · rw [Real.norm_eq_abs, abs_mul]
        nlinarith only [mul_le_mul_of_nonneg_left
          (shell_kernel_bound R W s t hR hW hh ht) (abs_nonneg (μ s))]
      · simp [hs s hh]))
  simpa only [Real.norm_eq_abs, integral_const_mul] using h

/-- Exact cancellation around the reference shell of radius R. Neither the
radiality of the core nor a sign condition on Q is required. -/
theorem shell_cancellation_identity (μ : ℝ → ℝ) (R W Q : ℝ)
    (_hR : 0 < R) (hμ : Integrable μ)
    (_hs : ∀ s, s ∉ Icc R (R + W) → μ s = 0)
    (hmass : ∫ s, μ s = -Q)
    (hint : Integrable (fun t => μ t * potential μ t)) :
    energy μ + Q * potential μ 0 = -Q ^ 2 / (2 * R) +
      (1 / 2 : ℝ) * (∫ t, μ t * (potential μ t + Q / R)) +
      Q * (potential μ 0 + Q / R) := by
  have hexpand : (∫ t, μ t * (potential μ t + Q / R)) =
      (∫ t, μ t * potential μ t) - Q ^ 2 / R := by
    simp_rw [mul_add]
    rw [integral_add hint (hμ.mul_const _), integral_mul_const, hmass]
    ring
  rw [hexpand]
  unfold energy
  ring

/-- The combined shell self-energy and charged core interaction cost surface
order. `L` controls the shell's total variation per unit surface area. -/
theorem shell_correction_bound (μ : ℝ → ℝ) (R W Q K L : ℝ)
    (hR : 0 < R) (hW : 0 ≤ W) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hμ : Integrable μ) (hs : ∀ s, s ∉ Icc R (R + W) → μ s = 0)
    (hmass : ∫ s, μ s = -Q) (hq : |Q| ≤ K * R ^ 2)
    (hL1 : ∫ s, |μ s| ≤ L * R ^ 2)
    (hint : Integrable (fun t => μ t * potential μ t)) :
    energy μ + Q * potential μ 0 ≤
      -Q ^ 2 / (2 * R) + W * (L ^ 2 / 2 + K * L) * R ^ 2 := by
  have hpoint (t : ℝ) (ht : t ≤ R + W) :
      |potential μ t + Q / R| ≤ W * L := by
    calc
      _ ≤ (W / R ^ 2) * ∫ s, |μ s| :=
        potential_remainder_bound μ R W Q t hR hW ht hμ hs hmass
      _ ≤ (W / R ^ 2) * (L * R ^ 2) :=
        mul_le_mul_of_nonneg_left hL1 (by positivity)
      _ = W * L := by field_simp
  have hi : |∫ t, μ t * (potential μ t + Q / R)| ≤ W * L ^ 2 * R ^ 2 := by
    have h := norm_integral_le_of_norm_le (hμ.abs.const_mul (W * L))
      (Filter.Eventually.of_forall (fun t : ℝ => show
        ‖μ t * (potential μ t + Q / R)‖ ≤ (W * L) * |μ t| from by
        by_cases ht : t ∈ Icc R (R + W)
        · rw [Real.norm_eq_abs, abs_mul]
          nlinarith only [mul_le_mul_of_nonneg_left (hpoint t ht.2) (abs_nonneg (μ t))]
        · simp [hs t ht]))
    rw [Real.norm_eq_abs, integral_const_mul] at h
    calc
      _ ≤ W * L * ∫ s, |μ s| := h
      _ ≤ W * L * (L * R ^ 2) :=
        mul_le_mul_of_nonneg_left hL1 (mul_nonneg hW hL)
      _ = _ := by ring
  have hc : |Q * (potential μ 0 + Q / R)| ≤ W * K * L * R ^ 2 := by
    rw [← potential_constant_inside μ R W R hR.le le_rfl hs]
    rw [abs_mul]
    calc
      _ ≤ (K * R ^ 2) * (W * L) :=
        mul_le_mul hq (hpoint R (by linarith)) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [shell_cancellation_identity μ R W Q hR hμ hs hmass hint]
  have ha := le_abs_self (∫ t, μ t * (potential μ t + Q / R))
  have hb := le_abs_self (Q * (potential μ 0 + Q / R))
  nlinarith only [hi, hc, ha, hb]

/-- The sign convention and outer-radius monopole term used in
`completion_shell_bound`. Here `Q` is the excess background charge of the
core and the shell has total charge `Q`. The core itself can be nonradial. -/
theorem shell_correction_bound_at_outer_radius (μ : ℝ → ℝ) (R S Q K L : ℝ)
    (hR : 0 < R) (hRS : R ≤ S) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hμ : Integrable μ) (hs : ∀ s, s ∉ Icc R S → μ s = 0)
    (hmass : ∫ s, μ s = Q) (hq : |Q| ≤ K * R ^ 2)
    (hL1 : ∫ s, |μ s| ≤ L * R ^ 2)
    (hint : Integrable (fun t => μ t * potential μ t)) :
    energy μ - Q * potential μ 0 ≤
      -Q ^ 2 / (2 * S) + (S - R) * (L ^ 2 / 2 + K * L) * R ^ 2 := by
  have hinner := shell_correction_bound μ R (S - R) (-Q) K L hR
    (sub_nonneg.mpr hRS) hK hL hμ
    (by simpa only [show R + (S - R) = S by ring] using hs)
    (by simpa only [neg_neg] using hmass) (by simpa only [abs_neg] using hq) hL1 hint
  have hmonopole : -Q ^ 2 / (2 * R) ≤ -Q ^ 2 / (2 * S) := by
    have h := div_le_div_of_nonneg_left (sq_nonneg Q) (by positivity : 0 < 2 * R)
      (mul_le_mul_of_nonneg_left hRS (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [neg_div] using neg_le_neg h
  simp only [neg_sq, neg_mul, ← sub_eq_add_neg] at hinner
  linarith only [hinner, hmonopole]

end Jellium.Neutralization
