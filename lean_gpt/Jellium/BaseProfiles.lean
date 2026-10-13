import Jellium.UpperConstruction

/-! The fixed neutral correction profiles used in periodic averaging, obtained
from the actual core states and compensated radial collars. -/

open Set Finset MeasureTheory

namespace Jellium.BaseProfiles

open UpperConstruction
universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable {State : Type w} {C : TrialState.ChargeModel Space V} {h₂ cTF : ℝ}
variable (S : TrialState.StateAPI C State h₂ cTF)
variable {n : ℕ} {a ρ sf κ e ε : ℝ}
variable (F : BallFamily n a) (R : LocalRepresentatives C F ρ) (cores : Fin n → State)

noncomputable def correction (i : Fin n) : V := S.density (cores i) - R.core i + R.collar i

variable (hc : CoreData S F R κ e ε cores)
variable (hpolar : RadialCollar.PolarLaw C.measure sf) (ha : 0 < a)

include hc hpolar ha in
theorem correction_integrable [IsFiniteMeasureOnCompacts C.measure] (i : Fin n) :
    Integrable (C.eval (correction S F R cores i)) C.measure := by
  have hq : Integrable (C.eval (R.core i)) C.measure := by
    rw [R.core_eval]
    exact core_integrable C _ _ _
  have hg : Integrable (C.eval (R.collar i)) C.measure := by
    rw [R.collar_eval]
    exact RadialCollar.charge_integrable hpolar _ ρ (F.radius_pos i) ha (F.collar_room i)
  simpa only [correction, map_add, map_sub, Pi.add_apply, Pi.sub_apply] using
    ((hc.integrable i).sub hq).add hg

include hc hpolar ha in
theorem correction_neutral (i : Fin n) :
    (∫ x, C.eval (correction S F R cores i) x ∂C.measure) = 0 := by
  have hg : C.mass (R.collar i) = 0 := by
    rw [C.mass_integral, R.collar_eval]
    exact RadialCollar.charge_neutral hpolar _ ρ (F.radius_pos i) ha (F.collar_room i)
  rw [← C.mass_integral]
  simp only [correction, map_add, map_sub, hc.neutral i, sub_self, zero_add, hg]

include hc ha in
theorem correction_support (i : Fin n) :
    Function.support (C.eval (correction S F R cores i)) ⊆
      Metric.closedBall (F.center i) (F.radius i + 2 * a) := by
  classical
  intro x hx
  by_contra hout
  have hd : C.eval (S.density (cores i)) x = 0 := by
    by_contra hne
    exact hout ((Metric.closedBall_subset_closedBall (by linarith)) (hc.support i hne))
  have hq : C.eval (R.core i) x = 0 := by
    rw [R.core_eval]
    have hdist : ¬ dist x (F.center i) ≤ F.radius i := by
      intro hd'
      exact hout (show dist x (F.center i) ≤ F.radius i + 2 * a by linarith)
    simp [RadialCollar.coreBackground, hdist]
  have hg : C.eval (R.collar i) x = 0 := by
    rw [R.collar_eval]
    exact RadialCollar.charge_outside (le_of_lt (lt_of_not_ge hout))
  change C.eval (correction S F R cores i) x ≠ 0 at hx
  exact hx (by simp [correction, hd, hq, hg])

end Jellium.BaseProfiles
