import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Bounds for the one-dimensional radial mass representation in Newton's
theorem. `mu s ds` is the charge in a spherical radial interval. The only
electrostatic identification needed is the usual radial Newton formula. -/

open MeasureTheory Set

namespace Jellium.RadialShells

noncomputable def potential (μ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s : ℝ, μ s * (1 / max t s)

theorem reciprocal_kernel_bound (r w s t : ℝ)
    (hr : 0 < r) (hw : 0 ≤ w) (hs : s ∈ Icc r (r + w)) :
    |1 / max t s - 1 / max t r| ≤ w / r ^ 2 := by
  have hA : r ≤ max t r := le_max_right _ _
  have hB : r ≤ max t s := le_trans hs.1 (le_max_right _ _)
  have hApos : 0 < max t r := lt_of_lt_of_le hr hA
  have hBpos : 0 < max t s := lt_of_lt_of_le hr hB
  have hAB : max t r ≤ max t s := max_le_max_left t hs.1
  have hwidth : max t s - max t r ≤ w := by
    by_cases htr : t ≤ r
    · rw [max_eq_right htr, max_eq_right (le_trans htr hs.1)]
      linarith [hs.2]
    · rw [max_eq_left (le_of_not_ge htr)]
      by_cases hts : t ≤ s
      · rw [max_eq_right hts]
        linarith [hs.2]
      · rw [max_eq_left (le_of_not_ge hts)]
        simpa using hw
  have hden : r ^ 2 ≤ max t r * max t s := by
    nlinarith [mul_le_mul hA hB (le_of_lt hr) (le_of_lt hApos)]
  have hinv : 1 / max t s ≤ 1 / max t r := one_div_le_one_div_of_le hApos hAB
  have heq : 1 / max t r - 1 / max t s =
      (max t s - max t r) / (max t r * max t s) := by
    field_simp
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hinv), heq]
  exact div_le_div₀ hw hwidth (sq_pos_of_pos hr) hden

theorem potential_integrable (μ : ℝ → ℝ) (r w t : ℝ)
    (hr : 0 < r) (hμ : Integrable μ)
    (hsupport : ∀ s, s ∉ Icc r (r + w) → μ s = 0) :
    Integrable (fun s : ℝ => μ s * (1 / max t s)) := by
  have hdom : Integrable (fun s : ℝ => (1 / r) * |μ s|) := hμ.abs.const_mul (1 / r)
  apply hdom.mono'
  · apply hμ.aestronglyMeasurable.mul
    simp only [one_div]
    exact (measurable_const.max measurable_id).inv.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro s
    by_cases hs : s ∈ Icc r (r + w)
    · have hd : r ≤ max t s := le_trans hs.1 (le_max_right _ _)
      have hi := one_div_le_one_div_of_le hr hd
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
        (one_div_nonneg.mpr (le_trans (le_of_lt hr) hd))]
      nlinarith [mul_le_mul_of_nonneg_left hi (abs_nonneg (μ s))]
    · simp [hsupport s hs]

/-- Neutrality removes the reference reciprocal exactly, before estimating. -/
theorem neutral_potential_representation (μ : ℝ → ℝ) (r w t : ℝ)
    (hr : 0 < r) (hμ : Integrable μ)
    (hsupport : ∀ s, s ∉ Icc r (r + w) → μ s = 0)
    (hneut : ∫ s : ℝ, μ s = 0) :
    potential μ t = ∫ s : ℝ, μ s * (1 / max t s - 1 / max t r) := by
  simp_rw [mul_sub]
  rw [integral_sub (potential_integrable μ r w t hr hμ hsupport)
    (hμ.mul_const (1 / max t r)), integral_mul_const, hneut, zero_mul, sub_zero]
  rfl

/-- The potential of a neutral shell is controlled by its thickness and L1 mass. -/
theorem neutral_potential_bound (μ : ℝ → ℝ) (r w t : ℝ)
    (hr : 0 < r) (hw : 0 ≤ w) (hμ : Integrable μ)
    (hsupport : ∀ s, s ∉ Icc r (r + w) → μ s = 0)
    (hneut : ∫ s : ℝ, μ s = 0) :
    |potential μ t| ≤ (w / r ^ 2) * ∫ s : ℝ, |μ s| := by
  rw [neutral_potential_representation μ r w t hr hμ hsupport hneut]
  have hbound := norm_integral_le_of_norm_le (hμ.abs.const_mul (w / r ^ 2))
    (Filter.Eventually.of_forall (fun s : ℝ => show
      ‖μ s * (1 / max t s - 1 / max t r)‖ ≤ w / r ^ 2 * |μ s| from by
        by_cases hs : s ∈ Icc r (r + w)
        · rw [Real.norm_eq_abs, abs_mul]
          have hk := reciprocal_kernel_bound r w s t hr hw hs
          nlinarith [mul_le_mul_of_nonneg_left hk (abs_nonneg (μ s))]
        · simp [hsupport s hs]))
  simpa only [Real.norm_eq_abs, integral_const_mul] using hbound

/-- The same Newton potential vanishes identically outside the shell. -/
theorem neutral_potential_zero_outside (μ : ℝ → ℝ) (r w t : ℝ)
    (hsupport : ∀ s, s ∉ Icc r (r + w) → μ s = 0)
    (hneut : ∫ s : ℝ, μ s = 0) (ht : r + w ≤ t) :
    potential μ t = 0 := by
  have hf : (fun s : ℝ => μ s * (1 / max t s)) = (fun s => μ s * (1 / t)) := by
    funext s
    by_cases hs : s ∈ Icc r (r + w)
    · rw [max_eq_left (le_trans hs.2 ht)]
    · simp [hsupport s hs]
  unfold potential
  rw [hf, integral_mul_const, hneut, zero_mul]

/-- Radial charge mass of a unit-density spherical layer. -/
noncomputable def layer (a b : ℝ) : ℝ → ℝ :=
  (Icc a b).indicator (fun s => 4 * Real.pi * s ^ 2)

noncomputable def layerMass (a b : ℝ) : ℝ :=
  (4 * Real.pi / 3) * (b ^ 3 - a ^ 3)

theorem layer_integrable (a b : ℝ) : Integrable (layer a b) := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact ((continuous_const.mul continuous_const).mul (continuous_id.pow 2)).integrableOn_Icc

theorem layer_nonnegative (a b s : ℝ) : 0 ≤ layer a b s := by
  unfold layer
  exact indicator_nonneg (fun _ _ => by positivity) _

theorem layer_integral (a b : ℝ) (hab : a ≤ b) :
    ∫ s : ℝ, layer a b s = layerMass a b := by
  unfold layer layerMass
  rw [integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_pow]
  norm_num
  ring

theorem layerMass_pos (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    0 < layerMass a b := by
  unfold layerMass
  have := pow_lt_pow_left₀ hab ha (by decide : 3 ≠ 0)
  positivity

/-- The compensation coefficient is fixed by exact neutrality. -/
noncomputable def compensated (a b c d : ℝ) (s : ℝ) : ℝ :=
  layer a b s - (layerMass a b / layerMass c d) * layer c d s

theorem compensated_integrable (a b c d : ℝ) :
    Integrable (compensated a b c d) :=
  (layer_integrable a b).sub ((layer_integrable c d).const_mul _)

theorem compensated_neutral (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hd : layerMass c d ≠ 0) :
    ∫ s : ℝ, compensated a b c d s = 0 := by
  unfold compensated
  rw [integral_sub (layer_integrable a b)
    ((layer_integrable c d).const_mul _), integral_const_mul,
    layer_integral a b hab, layer_integral c d hcd]
  field_simp
  ring

theorem compensated_support (a b c d r w : ℝ)
    (hab : Icc a b ⊆ Icc r (r + w)) (hcd : Icc c d ⊆ Icc r (r + w)) :
    ∀ s, s ∉ Icc r (r + w) → compensated a b c d s = 0 := by
  intro s hs
  have ha : s ∉ Icc a b := fun hi => hs (hab hi)
  have hc : s ∉ Icc c d := fun hi => hs (hcd hi)
  simp [compensated, layer, ha, hc]

theorem compensated_L1_bound (a b c d : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hc : 0 ≤ c) (hcd : c < d) :
    ∫ s : ℝ, |compensated a b c d s| ≤ 2 * layerMass a b := by
  have hA := layerMass_pos a b ha hab
  have hB := layerMass_pos c d hc hcd
  have hcoef : 0 ≤ layerMass a b / layerMass c d := div_nonneg hA.le hB.le
  calc
    _ ≤ ∫ s : ℝ, layer a b s +
        (layerMass a b / layerMass c d) * layer c d s := by
      apply integral_mono (compensated_integrable a b c d).abs
        ((layer_integrable a b).add ((layer_integrable c d).const_mul _))
      intro s
      unfold compensated
      calc
        _ ≤ |layer a b s| + |(layerMass a b / layerMass c d) * layer c d s| :=
          abs_sub _ _
        _ = _ := by
          rw [abs_of_nonneg (layer_nonnegative a b s),
            abs_of_nonneg (mul_nonneg hcoef (layer_nonnegative c d s))]
          rfl
    _ = 2 * layerMass a b := by
      rw [integral_add (layer_integrable a b) ((layer_integrable c d).const_mul _),
        integral_const_mul, layer_integral a b hab.le, layer_integral c d hcd.le]
      field_simp
      ring

/-- A universal volume estimate for any spherical layer of width `h`
inside radius `2R`. -/
theorem layerMass_bound (a b R h : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * R) (hwidth : b - a = h) :
    layerMass a b ≤ 16 * Real.pi * R ^ 2 * h := by
  have hh : 0 ≤ h := by linarith
  have hR : 0 ≤ R := by linarith
  have haR : a ≤ 2 * R := le_trans hab hb
  have ha2 : a ^ 2 ≤ 4 * R ^ 2 := by nlinarith
  have hb2 : b ^ 2 ≤ 4 * R ^ 2 := by nlinarith
  have hab2 : a * b ≤ 4 * R ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hpoly : b ^ 3 - a ^ 3 ≤ 12 * R ^ 2 * h := by
    have hfac : b ^ 3 - a ^ 3 = h * (a ^ 2 + a * b + b ^ 2) := by rw [← hwidth]; ring
    rw [hfac]
    nlinarith [mul_le_mul_of_nonneg_left (show a ^ 2 + a * b + b ^ 2 ≤ 12 * R ^ 2 by linarith) hh]
  unfold layerMass
  nlinarith [mul_le_mul_of_nonneg_left hpoly Real.pi_pos.le]

noncomputable def outer (R h : ℝ) : ℝ → ℝ :=
  compensated R (R + h) (R + h) (R + 2 * h)

noncomputable def inner (R h : ℝ) : ℝ → ℝ :=
  compensated (R - h) R (R - 2 * h) (R - h)

theorem outer_properties (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R) :
    Integrable (outer R h) ∧ (∫ s, outer R h s = 0) ∧
    (∀ s, s ∉ Icc R (R + 2 * h) → outer R h s = 0) ∧
    (∫ s, |outer R h s| ≤ 32 * Real.pi * R ^ 2 * h) := by
  have hR0 : 0 < R := by linarith
  refine ⟨compensated_integrable _ _ _ _, ?_, ?_, ?_⟩
  · apply compensated_neutral <;> try linarith
    exact ne_of_gt (layerMass_pos _ _ (by linarith) (by linarith))
  · apply compensated_support
    · intro s hs
      exact ⟨hs.1, by linarith [hs.2]⟩
    · intro s hs
      exact ⟨by linarith [hs.1], hs.2⟩
  · have hL := compensated_L1_bound R (R + h) (R + h) (R + 2 * h)
      hR0.le (by linarith) (by linarith) (by linarith)
    have hM := layerMass_bound R (R + h) R h hR0.le (by linarith)
      (by linarith) (by ring)
    change _ ≤ _ at hL
    exact le_trans hL (by nlinarith)

theorem inner_properties (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R) :
    Integrable (inner R h) ∧ (∫ s, inner R h s = 0) ∧
    (∀ s, s ∉ Icc (R - 2 * h) ((R - 2 * h) + 2 * h) → inner R h s = 0) ∧
    (∫ s, |inner R h s| ≤ 32 * Real.pi * R ^ 2 * h) := by
  refine ⟨compensated_integrable _ _ _ _, ?_, ?_, ?_⟩
  · apply compensated_neutral <;> try linarith
    exact ne_of_gt (layerMass_pos _ _ (by linarith) (by linarith))
  · apply compensated_support
    · intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · intro s hs
      exact ⟨hs.1, by linarith [hs.2]⟩
  · have hL := compensated_L1_bound (R - h) R (R - 2 * h) (R - h)
      (by linarith) (by linarith) (by linarith) (by linarith)
    have hM := layerMass_bound (R - h) R R h (by linarith) (by linarith)
      (by linarith) (by ring)
    exact le_trans hL (by nlinarith)

theorem thin_neutral_potential_bound (μ : ℝ → ℝ) (R h r t : ℝ)
    (hh : 0 ≤ h) (hR : 0 < R) (hr : R / 2 ≤ r) (hμ : Integrable μ)
    (hsupport : ∀ s, s ∉ Icc r (r + 2 * h) → μ s = 0)
    (hneut : ∫ s, μ s = 0)
    (hL1 : ∫ s, |μ s| ≤ 32 * Real.pi * R ^ 2 * h) :
    |potential μ t| ≤ 256 * Real.pi * h ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hk : 2 * h / r ^ 2 ≤ 8 * h / R ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hr0) (sq_pos_of_pos hR)).2
    have hrsq : R ^ 2 ≤ 4 * r ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hrsq hh]
  calc
    _ ≤ (2 * h / r ^ 2) * ∫ s, |μ s| :=
      neutral_potential_bound μ r (2 * h) t hr0 (by positivity) hμ hsupport hneut
    _ ≤ (8 * h / R ^ 2) * (32 * Real.pi * R ^ 2 * h) :=
      mul_le_mul hk hL1 (integral_nonneg (fun _ => abs_nonneg _)) (by positivity)
    _ = _ := by field_simp; ring

noncomputable def energy (μ : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t : ℝ, μ t * potential μ t

theorem energy_bound (μ : ℝ → ℝ) (P : ℝ) (hμ : Integrable μ)
    (hpotential : ∀ t, |potential μ t| ≤ P) :
    |energy μ| ≤ (1 / 2 : ℝ) * P * ∫ t, |μ t| := by
  have hbound := norm_integral_le_of_norm_le (hμ.abs.const_mul P)
    (Filter.Eventually.of_forall (fun t : ℝ => show
      ‖μ t * potential μ t‖ ≤ P * |μ t| from by
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [mul_le_mul_of_nonneg_left (hpotential t) (abs_nonneg (μ t))]))
  rw [Real.norm_eq_abs, integral_const_mul] at hbound
  unfold energy
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  nlinarith

theorem outer_potential_bound (R h t : ℝ) (hh : 0 < h) (hR : 4 * h < R) :
    |potential (outer R h) t| ≤ 256 * Real.pi * h ^ 2 := by
  obtain ⟨hi, hn, hs, hL⟩ := outer_properties R h hh hR
  exact thin_neutral_potential_bound _ R h R t hh.le (by linarith)
    (by linarith) hi hs hn hL

theorem inner_potential_bound (R h t : ℝ) (hh : 0 < h) (hR : 4 * h < R) :
    |potential (inner R h) t| ≤ 256 * Real.pi * h ^ 2 := by
  obtain ⟨hi, hn, hs, hL⟩ := inner_properties R h hh hR
  exact thin_neutral_potential_bound _ R h (R - 2 * h) t hh.le (by linarith)
    (by linarith) hi hs hn hL

theorem outer_energy_bound (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R) :
    |energy (outer R h)| ≤ 4096 * Real.pi ^ 2 * R ^ 2 * h ^ 3 := by
  obtain ⟨hi, _, _, hL⟩ := outer_properties R h hh hR
  have he := energy_bound _ _ hi (fun t => outer_potential_bound R h t hh hR)
  calc
    _ ≤ (1 / 2 : ℝ) * (256 * Real.pi * h ^ 2) * ∫ t, |outer R h t| := he
    _ ≤ (1 / 2 : ℝ) * (256 * Real.pi * h ^ 2) * (32 * Real.pi * R ^ 2 * h) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by ring

theorem inner_energy_bound (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R) :
    |energy (inner R h)| ≤ 4096 * Real.pi ^ 2 * R ^ 2 * h ^ 3 := by
  obtain ⟨hi, _, _, hL⟩ := inner_properties R h hh hR
  have he := energy_bound _ _ hi (fun t => inner_potential_bound R h t hh hR)
  calc
    _ ≤ (1 / 2 : ℝ) * (256 * Real.pi * h ^ 2) * ∫ t, |inner R h t| := he
    _ ≤ (1 / 2 : ℝ) * (256 * Real.pi * h ^ 2) * (32 * Real.pi * R ^ 2 * h) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by ring

theorem outer_potential_zero (R h t : ℝ) (hh : 0 < h) (hR : 4 * h < R)
    (ht : R + 2 * h ≤ t) : potential (outer R h) t = 0 := by
  obtain ⟨_, hn, hs, _⟩ := outer_properties R h hh hR
  exact neutral_potential_zero_outside _ R (2 * h) t hs hn ht

theorem inner_potential_zero (R h t : ℝ) (hh : 0 < h) (hR : 4 * h < R)
    (ht : R ≤ t) : potential (inner R h) t = 0 := by
  obtain ⟨_, hn, hs, _⟩ := inner_properties R h hh hR
  exact neutral_potential_zero_outside _ (R - 2 * h) (2 * h) t hs hn (by linarith)

theorem outer_ratio_bound (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R) :
    0 ≤ layerMass R (R + h) / layerMass (R + h) (R + 2 * h) ∧
    layerMass R (R + h) / layerMass (R + h) (R + 2 * h) ≤ 1 := by
  have hR0 : 0 < R := by linarith
  have hA := layerMass_pos R (R + h) (by linarith) (by linarith)
  have hB := layerMass_pos (R + h) (R + 2 * h) (by linarith) (by linarith)
  refine ⟨div_nonneg hA.le hB.le, (div_le_one hB).2 ?_⟩
  have hdiff : (R + 2 * h) ^ 3 - (R + h) ^ 3 - ((R + h) ^ 3 - R ^ 3) =
      6 * h ^ 2 * (R + h) := by ring
  have hpoly : (R + h) ^ 3 - R ^ 3 ≤ (R + 2 * h) ^ 3 - (R + h) ^ 3 := by
    have : 0 ≤ 6 * h ^ 2 * (R + h) := by positivity
    linarith
  exact mul_le_mul_of_nonneg_left hpoly (by positivity)

end Jellium.RadialShells
