import Jellium.TrialState
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! A bounded background potential controls the mixed Coulomb observable by
the actual mean particle number. This supplies continuum-mixture integrability. -/

open MeasureTheory

namespace Jellium.TrialState

universe u v
variable {X : Type u} [MeasurableSpace X]
variable {V : Type v} [AddCommGroup V] [Module ℝ V]

theorem mixed_coulomb_abs_le_mass
    (C : ChargeModel X V) (density background : V) {P : ℝ}
    (_hP : 0 ≤ P)
    (hpotential : ∀ x, |C.potential background x| ≤ P)
    (hint : Integrable (C.eval density) C.measure)
    (hdensity : ∀ x, 0 ≤ C.eval density x) :
    |C.coulomb.form density background| ≤ (P / 2) * C.mass density := by
  rw [C.coulomb.symmetric density background, C.coulomb_integral, abs_mul]
  have hpoint (x : X) : |C.potential background x * C.eval density x| ≤ P * C.eval density x := by
    rw [abs_mul, abs_of_nonneg (hdensity x)]
    exact mul_le_mul_of_nonneg_right (hpotential x) (hdensity x)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => abs_nonneg (C.potential background x * C.eval density x)))
    (hint.const_mul P) (Filter.Eventually.of_forall hpoint)
  have habs := abs_integral_le_integral_abs (f := fun x => C.potential background x * C.eval density x) (μ := C.measure)
  rw [integral_const_mul, ← C.mass_integral density] at hmono
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith

end Jellium.TrialState
