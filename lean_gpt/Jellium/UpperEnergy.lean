import Jellium.Variational
import Jellium.Localization
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp

/-! Integrating the actual finite-trial estimate and taking the box limit.
Signed core energy is retained throughout the exact integral computation. -/

open MeasureTheory Filter Topology

namespace Jellium.UpperEnergy

theorem finite_energy_bound
    {J occupied surface gradient mass R e ε h₂ ρ q C G κ rmin : ℝ}
    (hh₂ : 0 ≤ h₂) (hC : 0 ≤ C)
    (htrial : J ≤ (e + ε) * occupied + h₂ * gradient + C * surface +
      q * (mass - ρ * occupied))
    (hsurface : surface ≤ occupied / (κ * rmin))
    (hgradient : gradient ≤ G * R ^ 2) (hmass : mass = ρ * R ^ 3) :
    J ≤ (e + ε) * occupied + (q * ρ) * (R ^ 3 - occupied) +
      (C / (κ * rmin)) * occupied + (h₂ * G) * R ^ 2 := by
  have hg := mul_le_mul_of_nonneg_left hgradient hh₂
  have hs := mul_le_mul_of_nonneg_left hsurface hC
  rw [hmass] at htrial
  have hid : C * (occupied / (κ * rmin)) = C / (κ * rmin) * occupied := by ring
  rw [hid] at hs
  nlinarith

theorem finite_uniform_bound
    {U : Type*} (trial occupied surface : U → ℝ)
    {A B D ρ mass gradient Qv Qs : ℝ}
    (hv : ∀ u, |occupied u| ≤ Qv) (hs : ∀ u, |surface u| ≤ Qs)
    (htrial : ∀ u, trial u ≤ A * occupied u + gradient + B * surface u +
      D * (mass - ρ * occupied u)) :
    ∀ u, trial u ≤ |A - D * ρ| * Qv + |B| * Qs + gradient + D * mass := by
  intro u
  have hv' : (A - D * ρ) * occupied u ≤ |A - D * ρ| * Qv := by
    calc
      _ ≤ |(A - D * ρ) * occupied u| := le_abs_self _
      _ = |A - D * ρ| * |occupied u| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hv u) (abs_nonneg _)
  have hs' : B * surface u ≤ |B| * Qs := by
    calc
      _ ≤ |B * surface u| := le_abs_self _
      _ = |B| * |surface u| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs u) (abs_nonneg _)
  nlinarith [htrial u]

theorem average_trial_bound
    {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (trial occupied : U → ℝ) {R e ε K c B : ℝ}
    (htrial : Integrable trial μ) (hoccupied : Integrable occupied μ)
    (hbound : ∀ u, trial u ≤ (e + ε) * occupied u +
      K * (R ^ 3 - occupied u) + c * occupied u + B * R ^ 2) :
    (∫ u, trial u ∂μ) ≤
      (e + ε + c - K) * (∫ u, occupied u ∂μ) + K * R ^ 3 + B * R ^ 2 := by
  have hpoint (u : U) : trial u ≤
      (e + ε + c - K) * occupied u + (K * R ^ 3 + B * R ^ 2) := by
    nlinarith [hbound u]
  have h := integral_mono htrial
    ((hoccupied.const_mul (e + ε + c - K)).add (integrable_const (K * R ^ 3 + B * R ^ 2))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (f := fun u => (e + ε + c - K) * occupied u)
    (g := fun _ => K * R ^ 3 + B * R ^ 2)
    (hoccupied.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h
  linarith

theorem box_limit_bound
    {densityEnergy averageTrial occupied : ℝ → ℝ} {eU eJ ε K c B θ : ℝ}
    (hbulk : ∀ η : ℝ, 0 < η → ∀ᶠ R in atTop, eU - η ≤ densityEnergy R / R ^ 3)
    (hvariational : ∀ᶠ R in atTop, densityEnergy R ≤ averageTrial R)
    (htrial : ∀ᶠ R in atTop, averageTrial R ≤
      (eJ + ε + c - K) * occupied R + K * R ^ 3 + B * R ^ 2)
    (hcoverage : Tendsto (fun R => occupied R / R ^ 3) atTop (𝓝 θ)) :
    eU ≤ θ * (eJ + ε) + K * (1 - θ) + c * θ := by
  let upper : ℝ → ℝ := fun R => (eJ + ε + c - K) * (occupied R / R ^ 3) + K + B / R
  have hB : Tendsto (fun R : ℝ => B / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ))).const_mul B
  have hupper : Tendsto upper atTop (𝓝 (θ * (eJ + ε) + K * (1 - θ) + c * θ)) := by
    have h := ((hcoverage.const_mul (eJ + ε + c - K)).add_const K).add hB
    have heq : (eJ + ε + c - K) * θ + K + 0 = θ * (eJ + ε) + K * (1 - θ) + c * θ := by ring
    rw [heq] at h
    exact h
  have hle : ∀ᶠ R in atTop, densityEnergy R / R ^ 3 ≤ upper R := by
    filter_upwards [hvariational, htrial, eventually_gt_atTop (0 : ℝ)] with R hvar htr hR
    have hdiv := div_le_div_of_nonneg_right (hvar.trans htr) (pow_nonneg hR.le 3)
    have heq : ((eJ + ε + c - K) * occupied R + K * R ^ 3 + B * R ^ 2) / R ^ 3 = upper R := by
      dsimp [upper]
      field_simp
    simpa only [heq] using hdiv
  by_contra hnot
  let limit := θ * (eJ + ε) + K * (1 - θ) + c * θ
  have hgap : 0 < eU - limit := sub_pos.mpr (lt_of_not_ge hnot)
  let η := (eU - limit) / 3
  have hη : 0 < η := div_pos hgap (by norm_num)
  have hnear := (tendsto_order.1 hupper).2 (limit + η) (by dsimp [limit]; linarith)
  obtain ⟨R, hlow, hRle, hRnear⟩ := ((hbulk η hη).and (hle.and hnear)).exists
  dsimp [η] at hlow hRnear
  linarith

theorem packing_limit_bound
    {densityEnergy averageTrial occupied : ℝ → ℝ} {eU eJ ε K c B θ : ℝ}
    (hc : 0 ≤ c) (hθ : θ ≤ 1)
    (hbulk : ∀ η : ℝ, 0 < η → ∀ᶠ R in atTop, eU - η ≤ densityEnergy R / R ^ 3)
    (hvariational : ∀ᶠ R in atTop, densityEnergy R ≤ averageTrial R)
    (htrial : ∀ᶠ R in atTop, averageTrial R ≤
      (eJ + ε + c - K) * occupied R + K * R ^ 3 + B * R ^ 2)
    (hcoverage : Tendsto (fun R => occupied R / R ^ 3) atTop (𝓝 θ)) :
    eU ≤ θ * (eJ + ε) + K * (1 - θ) + c := by
  have h := box_limit_bound hbulk hvariational htrial hcoverage
  have hmul := mul_le_mul_of_nonneg_left hθ hc
  linarith

/-- Uniform counting controls either sign of the coefficient multiplying the
occupied volume. The remainder is explicit before taking the box limit. -/
theorem normalized_bound_of_counting
    {J V R e ε K c B θ H : ℝ} (hR : 0 < R)
    (htrial : J ≤ (e + ε + c - K) * V + K * R ^ 3 + B * R ^ 2)
    (hcount : |V - θ * R ^ 3| ≤ H * R ^ 2) :
    J / R ^ 3 ≤ θ * (e + ε) + K * (1 - θ) + c * θ +
      (|e + ε + c - K| * H + B) / R := by
  have herr : (e + ε + c - K) * (V - θ * R ^ 3) ≤
      |e + ε + c - K| * (H * R ^ 2) := by
    calc
      _ ≤ |(e + ε + c - K) * (V - θ * R ^ 3)| := le_abs_self _
      _ = |e + ε + c - K| * |V - θ * R ^ 3| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount (abs_nonneg _)
  apply (div_le_iff₀ (pow_pos hR 3)).2
  have hcancel : (|e + ε + c - K| * H + B) / R * R ^ 3 =
      (|e + ε + c - K| * H + B) * R ^ 2 := by field_simp
  have hid : (θ * (e + ε) + K * (1 - θ) + c * θ +
      (|e + ε + c - K| * H + B) / R) * R ^ 3 =
      (θ * (e + ε) + K * (1 - θ) + c * θ) * R ^ 3 +
        (|e + ε + c - K| * H + B) * R ^ 2 := by rw [add_mul, hcancel]
  rw [hid]
  nlinarith

end Jellium.UpperEnergy
