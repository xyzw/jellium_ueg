import Jellium.Lower
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp

/-! Normalized energy convergence for the constructed unitary dilation.
Only the standard dilation law, kinetic positivity and LO lower bound are
inputs. No convergence of the constructed trial energy is assumed. -/

open Filter Topology

namespace Jellium

theorem contracted_energy_tendsto
    {kinetic indirect volume factor : ℕ → ℝ} {h₂ K e : ℝ}
    (hh₂ : 0 < h₂) (hK : 0 ≤ K)
    (hvolume : ∀ n, 0 < volume n)
    (hkinetic : ∀ n, 0 ≤ kinetic n)
    (hLO : ∀ᶠ n in atTop, -K * volume n ≤ indirect n)
    (henergy : Tendsto (fun n => (h₂ * kinetic n + indirect n) / volume n) atTop (𝓝 e))
    (hfactor : Tendsto factor atTop (𝓝 1))
    (hfactor_range : ∀ᶠ n in atTop, (1 : ℝ) / 2 ≤ factor n ∧ factor n ≤ 1) :
    Tendsto (fun n => ((factor n)⁻¹ ^ 2 * (h₂ * kinetic n) +
      (factor n)⁻¹ * indirect n) / volume n) atTop (𝓝 e) := by
  let C := |e| + 1 + K
  have hnear : ∀ᶠ n in atTop, (h₂ * kinetic n + indirect n) / volume n ≤ C := by
    have hupper : e < C := by dsimp [C]; linarith [le_abs_self e]
    exact ((tendsto_order.1 henergy).2 C hupper).mono (fun _ h => h.le)
  have hbound : ∀ᶠ n in atTop,
      ‖((factor n)⁻¹ ^ 2 * (h₂ * kinetic n) + (factor n)⁻¹ * indirect n -
        (h₂ * kinetic n + indirect n)) / volume n‖ ≤ 24 * C * (1 - factor n) := by
    filter_upwards [hnear, hLO, hfactor_range] with n hn hlo ha
    have he : h₂ * kinetic n + indirect n ≤ C * volume n :=
      (div_le_iff₀ (hvolume n)).1 hn
    have hilo : -(C * volume n) ≤ indirect n := by
      have hKC : K ≤ C := by dsimp [C]; linarith [abs_nonneg e]
      have hmul := mul_le_mul_of_nonneg_right hKC (hvolume n).le
      linarith
    obtain ⟨hT, hI⟩ := separate_energy_bounds (kinetic n) (indirect n)
      (h₂ * kinetic n + indirect n) h₂ C (volume n) hh₂ (hkinetic n) rfl he hilo
    have hT' : h₂ * kinetic n ≤ 2 * C * volume n := by
      have h := (le_div_iff₀ hh₂).1 hT
      nlinarith
    have hsum : h₂ * kinetic n + |indirect n| ≤ 3 * C * volume n := by linarith
    have hcost := contraction_energy_error (factor n) (h₂ * kinetic n) (indirect n)
      ha.1 ha.2 (mul_nonneg hh₂.le (hkinetic n))
    have hcost' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 8 * (1 - factor n) by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hvolume n)]
    apply (div_le_iff₀ (hvolume n)).2
    nlinarith
  have hsmall : Tendsto (fun n => 24 * C * (1 - factor n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.sub hfactor : Tendsto (fun n => (1 : ℝ) - factor n) atTop (𝓝 (1 - 1))).const_mul (24 * C)
  have hdiff := squeeze_zero_norm' hbound hsmall
  have hsum := hdiff.add henergy
  convert hsum using 1
  · funext n
    ring
  · simp

end Jellium
