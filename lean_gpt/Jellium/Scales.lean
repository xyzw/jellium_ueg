import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Explicit neutral radii, smoothing widths and contraction factors for the
lower construction. The integer charge is (n+1)^6. -/

open Filter Topology

namespace Jellium.Scales

noncomputable def neutralScale (ρ κ : ℝ) : ℝ :=
  ((ρ * κ)⁻¹) ^ ((3 : ℝ)⁻¹)

theorem neutralScale_pos {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    0 < neutralScale ρ κ := Real.rpow_pos_of_pos (by positivity) _

theorem neutralScale_cube {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    ρ * κ * neutralScale ρ κ ^ 3 = 1 := by
  have hpow : neutralScale ρ κ ^ 3 = (ρ * κ)⁻¹ := by
    exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
  rw [hpow]
  exact mul_inv_cancel₀ (ne_of_gt (mul_pos hρ hκ))

def size (n : ℕ) : ℝ := (n : ℝ) + 1

noncomputable def radius (b : ℝ) (n : ℕ) : ℝ := b * size n ^ 2

noncomputable def width (n : ℕ) : ℝ := (size n)⁻¹

noncomputable def factor (b A : ℝ) (n : ℕ) : ℝ := 1 - (2 * A / b) * (size n)⁻¹ ^ 3

theorem size_pos (n : ℕ) : 0 < size n := by unfold size; positivity

theorem size_tendsto : Tendsto size atTop atTop := by
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

theorem neutral_radius {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) (n : ℕ) :
    ρ * (κ * radius (neutralScale ρ κ) n ^ 3) = (((n + 1) ^ 6 : ℕ) : ℝ) := by
  have hcube := neutralScale_cube hρ hκ
  calc
    _ = (ρ * κ * neutralScale ρ κ ^ 3) * size n ^ 6 := by unfold radius; ring
    _ = size n ^ 6 := by rw [hcube, one_mul]
    _ = _ := by simp [size]

theorem radius_tendsto {b : ℝ} (hb : 0 < b) : Tendsto (radius b) atTop atTop :=
  ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp size_tendsto).const_mul_atTop hb

theorem factor_eq {b : ℝ} (hb : 0 < b) (A : ℝ) (n : ℕ) :
    factor b A n = 1 - 2 * A * width n / radius b n := by
  have hs : size n ≠ 0 := ne_of_gt (size_pos n)
  unfold factor width radius
  field_simp

theorem factor_tendsto (b A : ℝ) : Tendsto (factor b A) atTop (𝓝 1) := by
  have hi : Tendsto (fun n => (size n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp size_tendsto
  change Tendsto (fun n => 1 - (2 * A / b) * (size n)⁻¹ ^ 3) atTop (𝓝 1)
  simpa only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero, sub_zero] using
    tendsto_const_nhds.sub (tendsto_const_nhds.mul (hi.pow 3))

theorem factor_eventually {b A : ℝ} (hb : 0 < b) (hA : 0 < A) :
    ∀ᶠ n in atTop, (1 : ℝ) / 2 < factor b A n ∧ factor b A n < 1 := by
  have hhalf := (tendsto_order.1 (factor_tendsto b A)).1 (1 / 2) (by norm_num)
  filter_upwards [hhalf] with n hn
  refine ⟨hn, ?_⟩
  have hpos : 0 < (2 * A / b) * (size n)⁻¹ ^ 3 := by
    have hs := size_pos n
    positivity
  unfold factor
  linarith

theorem smoothing_ratio_tendsto {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Tendsto (fun n => (width n / factor b A n) / radius b n) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp size_tendsto
  simp only [Function.comp_def] at hi
  have ha := (factor_tendsto b A).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h := (hi.pow 3).mul ha
  have hd := h.div_const b
  convert hd using 1
  · funext n
    unfold width radius
    field_simp
  · norm_num

theorem smoothing_product_tendsto {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Tendsto (fun n => (width n / factor b A n) * radius b n) atTop atTop := by
  have ha : Tendsto (fun n => b * (factor b A n)⁻¹) atTop (𝓝 b) := by
    simpa using tendsto_const_nhds.mul ((factor_tendsto b A).inv₀ (by norm_num : (1 : ℝ) ≠ 0))
  have h := ha.pos_mul_atTop hb size_tendsto
  convert h using 1
  funext n
  have hs : size n ≠ 0 := ne_of_gt (size_pos n)
  unfold width radius
  field_simp



noncomputable def safeFactor (b A : ℝ) (n : ℕ) : ℝ := max (1 / 2) (factor b A n)

theorem safeFactor_half (b A : ℝ) (n : ℕ) : (1 : ℝ) / 2 ≤ safeFactor b A n := le_max_left _ _

theorem safeFactor_pos (b A : ℝ) (n : ℕ) : 0 < safeFactor b A n :=
  lt_of_lt_of_le (by norm_num) (safeFactor_half b A n)

theorem safeFactor_le_one {b A : ℝ} (hb : 0 < b) (hA : 0 ≤ A) (n : ℕ) :
    safeFactor b A n ≤ 1 := by
  apply max_le (by norm_num)
  have hs := size_pos n
  have hterm : 0 ≤ (2 * A / b) * (size n)⁻¹ ^ 3 := by positivity
  unfold factor
  linarith

theorem safeFactor_eventually_eq {b A : ℝ} (hb : 0 < b) (hA : 0 < A) :
    safeFactor b A =ᶠ[atTop] factor b A := by
  filter_upwards [factor_eventually hb hA] with n hn
  exact max_eq_right hn.1.le

theorem safeFactor_tendsto {b A : ℝ} (hb : 0 < b) (hA : 0 < A) :
    Tendsto (safeFactor b A) atTop (𝓝 1) :=
  (factor_tendsto b A).congr' (safeFactor_eventually_eq hb hA).symm

theorem safe_smoothing_ratio_tendsto {b A : ℝ} (hb : 0 < b) (hA : 0 < A) :
    Tendsto (fun n => (width n / safeFactor b A n) / radius b n) atTop (𝓝 0) := by
  apply (smoothing_ratio_tendsto hb A).congr'
  filter_upwards [safeFactor_eventually_eq hb hA] with n hn
  rw [hn]

theorem safe_smoothing_product_tendsto {b A : ℝ} (hb : 0 < b) (hA : 0 < A) :
    Tendsto (fun n => (width n / safeFactor b A n) * radius b n) atTop atTop := by
  apply (smoothing_product_tendsto hb A).congr'
  filter_upwards [safeFactor_eventually_eq hb hA] with n hn
  rw [hn]

end Jellium.Scales
