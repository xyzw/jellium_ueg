import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
Quantitative and limiting steps of the canonical lower comparison.
The analytic construction of the contracted states and the applicability of
Lieb--Narnhofer to the disconnected domains are not supplied by this file.
-/

namespace Jellium

/-- Nonnegative kinetic energy and a lower bound on the indirect interaction
give separate extensive bounds. No sign assumption on the total energy. -/
theorem separate_energy_bounds (T I E h C V : ℝ)
    (hh : 0 < h) (hT : 0 ≤ T)
    (henergy : h * T + I = E) (hupper : E ≤ C * V)
    (hlower : -(C * V) ≤ I) :
    T ≤ (2 * C * V) / h ∧ |I| ≤ C * V := by
  constructor
  · apply (le_div_iff₀ hh).2
    nlinarith
  · apply abs_le.mpr
    constructor
    · exact hlower
    · nlinarith

/-- A contraction by a in [1/2, 1] has the linear error needed in the proof. -/
theorem inverse_contraction_bounds (a : ℝ) (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ a⁻¹ - 1 ∧ a⁻¹ - 1 ≤ 2 * (1 - a) ∧
    0 ≤ a⁻¹ ^ 2 - 1 ∧ a⁻¹ ^ 2 - 1 ≤ 8 * (1 - a) := by
  have ha0 : 0 < a := by linarith
  have hne : a ≠ 0 := ne_of_gt ha0
  have hi : a * a⁻¹ = 1 := mul_inv_cancel₀ hne
  have hb : 0 < a⁻¹ := inv_pos.mpr ha0
  have hi1 : 1 ≤ a⁻¹ := by nlinarith
  have hi2 : a⁻¹ ≤ 2 := by nlinarith
  have hfirst : a⁻¹ - 1 ≤ 2 * (1 - a) := by nlinarith
  refine ⟨by linarith, hfirst, by nlinarith, ?_⟩
  nlinarith

/-- Scaling the kinetic and indirect Coulomb terms gives a controlled error. -/
theorem contraction_energy_error (a kinetic indirect : ℝ)
    (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) (hk : 0 ≤ kinetic) :
    |(a⁻¹ ^ 2 * kinetic + a⁻¹ * indirect) - (kinetic + indirect)| ≤
      8 * (1 - a) * (kinetic + |indirect|) := by
  obtain ⟨h1, h2, h3, h4⟩ := inverse_contraction_bounds a ha ha1
  have hid : (a⁻¹ ^ 2 * kinetic + a⁻¹ * indirect) - (kinetic + indirect) =
      (a⁻¹ ^ 2 - 1) * kinetic + (a⁻¹ - 1) * indirect := by ring
  rw [hid]
  calc
    |(a⁻¹ ^ 2 - 1) * kinetic + (a⁻¹ - 1) * indirect| ≤
        |(a⁻¹ ^ 2 - 1) * kinetic| + |(a⁻¹ - 1) * indirect| := abs_add_le _ _
    _ = (a⁻¹ ^ 2 - 1) * kinetic + (a⁻¹ - 1) * |indirect| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg hk, abs_of_nonneg h1]
    _ ≤ 8 * (1 - a) * (kinetic + |indirect|) := by
      have h5 := mul_le_mul_of_nonneg_right h4 hk
      have h6 := mul_le_mul_of_nonneg_right h2 (abs_nonneg indirect)
      have h7 : 0 ≤ (1 - a) * |indirect| := mul_nonneg (by linarith) (abs_nonneg _)
      nlinarith

/-- The final lower-comparison argument for normalized energy sequences.
`canonicalApprox` must be produced by the actual canonicalization construction.
It is a hypothesis, not a claimed result of the formalization.
-/
theorem lower_comparison_of_sequences
    (eJ eU : ℝ) (trial canonicalApprox error : ℕ → ℝ)
    (htrial : Filter.Tendsto trial Filter.atTop (nhds eU))
    (hcanonical : Filter.Tendsto canonicalApprox Filter.atTop (nhds eJ))
    (herror : Filter.Tendsto error Filter.atTop (nhds 0))
    (hcomparison : ∀ᶠ n in Filter.atTop, canonicalApprox n ≤ trial n + error n) :
    eJ ≤ eU := by
  have hsum := htrial.add herror
  have hle := le_of_tendsto_of_tendsto hcanonical hsum hcomparison
  simpa using hle

end Jellium
