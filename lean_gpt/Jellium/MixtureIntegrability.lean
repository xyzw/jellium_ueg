import Jellium.Variational
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Normed.Group.Real

/-! Continuum mixture integrability follows from nonnegative kinetic and
repulsion observables, a uniform finite Jellium bound and the standard bounded
background-potential estimate at fixed mean particle number. -/

open MeasureTheory

namespace Jellium.Variational

theorem mixture_observables_integrable
    {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (kinetic repulsion cross : U → ℝ) {h₂ self Jmax Dmax : ℝ}
    (hh₂ : 0 < h₂)
    (hTmeas : AEMeasurable kinetic μ)
    (hWmeas : AEMeasurable repulsion μ)
    (hDmeas : AEMeasurable cross μ)
    (hT : ∀ᵐ u ∂μ, 0 ≤ kinetic u)
    (hW : ∀ᵐ u ∂μ, 0 ≤ repulsion u)
    (hD : ∀ᵐ u ∂μ, |cross u| ≤ Dmax)
    (hJ : ∀ᵐ u ∂μ, h₂ * kinetic u + repulsion u - 2 * cross u + self ≤ Jmax) :
    Integrable kinetic μ ∧ Integrable repulsion μ ∧ Integrable cross μ := by
  let M := |Jmax| + 2 * |Dmax| + |self|
  have hbound : ∀ᵐ u ∂μ, kinetic u ≤ M / h₂ ∧ repulsion u ≤ M := by
    filter_upwards [hT, hW, hD, hJ] with u ht hw hd hj
    have hcross : cross u ≤ |Dmax| :=
      (le_abs_self _).trans (hd.trans (le_abs_self _))
    have htotal : h₂ * kinetic u + repulsion u ≤ M := by
      dsimp [M]
      linarith [le_abs_self Jmax, neg_le_abs self]
    constructor
    · apply (le_div_iff₀ hh₂).2
      nlinarith
    · nlinarith [mul_nonneg hh₂.le ht]
  have hTint : Integrable kinetic μ := by
    apply Integrable.mono' (integrable_const (M / h₂)) hTmeas.aestronglyMeasurable
    filter_upwards [hT, hbound] with u ht hb
    simpa only [Real.norm_eq_abs, abs_of_nonneg ht] using hb.1
  have hWint : Integrable repulsion μ := by
    apply Integrable.mono' (integrable_const M) hWmeas.aestronglyMeasurable
    filter_upwards [hW, hbound] with u hw hb
    simpa only [Real.norm_eq_abs, abs_of_nonneg hw] using hb.2
  have hDint : Integrable cross μ := by
    apply Integrable.mono' (integrable_const Dmax) hDmeas.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hD
  exact ⟨hTint, hWint, hDint⟩

end Jellium.Variational
