import Jellium.PeriodicTrial
import Jellium.SelectedConstruction
import Jellium.Coverage
import Jellium.UpperCoverage

/-! The actual periodic, selected, vacuum-padded state family. Every core at
every shift is a translation of one fixed base state. -/

open Set Finset MeasureTheory Classical

namespace Jellium.PeriodicSelected

open UpperConstruction MeasurableTrial
abbrev Space := RadialCollar.Space
universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable {State : Type w} [MeasurableSpace State]
variable {C : TrialState.ChargeModel Space V} {h₂ cTF sf a ρ L : ℝ} {m : ℕ}
variable (S : TrialState.StateAPI C State h₂ cTF) (D : SobolevDirichlet C S sf)
variable (T : ChargeTranslations C) (A : StateTranslations C S T)
variable (O : FockOperations C S)
variable (F : BallFamily m a) (R : LocalRepresentatives C F ρ)
variable (s : Finset Spatial.LatticeIndex)

noncomputable def selection (L Rbox : ℝ) (j : Fin (Fintype.card (Fin m × s))) (u : Space) : Prop :=
  Spatial.selectedBall (Spatial.cube Rbox) a
    (F.center (PeriodicTrial.copyIndex m s j).1 +
      Spatial.latticeShift L (PeriodicTrial.copyIndex m s j).2.val + u)
    (F.radius (PeriodicTrial.copyIndex m s j).1 + 2 * a)


theorem sum_selected {W : Type*} [AddCommMonoid W] (L Rbox : ℝ) (w : Fin m → W) (u : Space) :
    (∑ j, if selection F s L Rbox j u then w (PeriodicTrial.copyIndex m s j).1 else 0) =
      ∑ i, ∑ z ∈ s, if Spatial.selectedBall (Spatial.cube Rbox) a
        (F.center i + Spatial.latticeShift L z + u) (F.radius i + 2 * a) then w i else 0 := by
  exact PeriodicTrial.sum_copyIndex m s (fun i z =>
    if Spatial.selectedBall (Spatial.cube Rbox) a
      (F.center i + Spatial.latticeShift L z + u) (F.radius i + 2 * a) then w i else 0)

noncomputable def coreCharge (L : ℝ) (j : Fin (Fintype.card (Fin m × s))) (u : Space) : V :=
  T.map (PeriodicTrial.shift s L u j) (R.core (PeriodicTrial.copyIndex m s j).1)

noncomputable def collarCharge (L : ℝ) (j : Fin (Fintype.card (Fin m × s))) (u : Space) : V :=
  T.map (PeriodicTrial.shift s L u j) (R.collar (PeriodicTrial.copyIndex m s j).1)

noncomputable def coreState (L : ℝ) (base : Fin m → State)
    (j : Fin (Fintype.card (Fin m × s))) (u : Space) : State :=
  A.map (PeriodicTrial.shift s L u j) (base (PeriodicTrial.copyIndex m s j).1)

noncomputable def trial (L Rbox M : ℝ) (β : V) (base : Fin m → State) (u : Space) : State :=
  MeasurableTrial.trial O M β (selection F s L Rbox)
    (coreCharge T F R s L) (collarCharge T F R s L) (coreState S T A s L base) u

theorem selection_measurable (L Rbox : ℝ) (ha : 0 ≤ a)
    (j : Fin (Fintype.card (Fin m × s))) : MeasurableSet {u | selection F s L Rbox j u} := by
  exact Lattice.measurableSet_selectedBall L Rbox a
    (F.radius (PeriodicTrial.copyIndex m s j).1 + 2 * a)
    (F.center (PeriodicTrial.copyIndex m s j).1) (PeriodicTrial.copyIndex m s j).2.val ha
    (by have := F.radius_pos (PeriodicTrial.copyIndex m s j).1; linarith)

theorem trial_measurable [MeasurableAdd₂ V] [MeasurableSub₂ V]
    (L Rbox M : ℝ) (β : V) (base : Fin m → State) (ha : 0 ≤ a) :
    Measurable (trial S T A O F R s L Rbox M β base) := by
  apply MeasurableTrial.trial_measurable O M β (selection F s L Rbox)
    (coreCharge T F R s L) (collarCharge T F R s L) (coreState S T A s L base)
    (selection_measurable F s L Rbox ha)
  · intro j
    exact translatedCharge_measurable T _ _ (measurable_const.add measurable_id)
  · intro j
    exact translatedCharge_measurable T _ _ (measurable_const.add measurable_id)
  · intro j
    exact translatedState_measurable T A _ _ (measurable_const.add measurable_id)

variable (hL : 0 < L)
variable (hinside : ∀ i, Metric.closedBall (F.center i) (F.radius i + 2 * a) ⊆ Spatial.cube L)

include hL hinside in
theorem trial_eq_padded (Rbox M : ℝ) (β : V) (base : Fin m → State) (u : Space) :
    trial S T A O F R s L Rbox M β base u =
      SelectedConstruction.paddedTrial S (PeriodicTrial.family F s hL hinside u) (PeriodicTrial.representatives T F R s hL hinside u)
        (fun j => selection F s L Rbox j u) β O M (PeriodicTrial.cores S T A (L := L) s base u) := rfl

include hL hinside in
/-- Exact density, requiring no Coulomb or upper-energy estimates. -/
theorem trial_density (hpolar : RadialCollar.PolarLaw C.measure sf)
    (ha : 0 < a) (hρ : 0 ≤ ρ) {M : ℝ}
    (base : Fin m → State)
    (hsupport : ∀ i, Function.support (C.eval (S.density (base i))) ⊆
      Metric.closedBall (F.center i) (F.radius i))
    (hM : 0 < M) (hcap : RadialCollar.amplitude * ρ ≤ M)
    (Rbox : ℝ) (β : V) (hβ0 : ∀ x, 0 ≤ C.eval β x) (hβle : ∀ x, C.eval β x ≤ ρ)
    (hβplateau : ∀ x ∈ Spatial.cube (Rbox - 2 * a), C.eval β x = ρ)
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) (u : Space) :
    S.density (trial S T A O F R s L Rbox M β base u) = β +
      (∑ j, if selection F s L Rbox j u then
        S.density (coreState S T A s L base j u) - coreCharge T F R s L j u else 0) +
      ∑ j, if selection F s L Rbox j u then collarCharge T F R s L j u else 0 := by
  let Fu := PeriodicTrial.family F s hL hinside u
  let Ru := PeriodicTrial.representatives T F R s hL hinside u
  have hplateau : ∀ j, selection F s L Rbox j u →
      ∀ x ∈ Metric.closedBall (Fu.center j) (Fu.radius j + 2 * a), C.eval β x = ρ := by
    intro j hj x hx
    apply hβplateau x
    rw [← Lattice.eroded_cube_eq Rbox a ha.le]
    exact hj hx
  have hs : ∀ j, Function.support (C.eval (S.density
      (PeriodicTrial.cores S T A (L := L) s base u j))) ⊆ Metric.closedBall (Fu.center j) (Fu.radius j) := by
    intro j
    simpa only [Fu, PeriodicTrial.cores, PeriodicTrial.family, PeriodicTrial.shift, add_assoc] using
      PeriodicTrial.shifted_support S T A (hsupport (PeriodicTrial.copyIndex m s j).1)
        (PeriodicTrial.shift s L u j)
  have h := SelectedConstruction.paddedTrial_density S D Fu Ru (fun j => selection F s L Rbox j u)
    ha hρ β hβ0 hβle hplateau O hpolar (PeriodicTrial.cores S T A (L := L) s base u)
    hs hM hcap hβmem
  rw [trial_eq_padded S T A O F R s hL hinside]
  exact h

include hL hinside in
/-- The final finite-periodic trial family, with exact density and fixed mean
mass, and the quantitative upper estimate proved from the core data and the
explicit collar/fluid construction. -/
theorem trial_bounds [IsFiniteMeasureOnCompacts C.measure]
    (Laws : CoulombLaws C sf) (hsf : 0 ≤ sf) (hh₂ : 0 ≤ h₂) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hpreserve : ∀ u : Space, MeasurePreserving (fun x : Space => x - u) C.measure C.measure)
    {κ e ε M K : ℝ}
    (hKcost : ∀ (z : Space) (r a ρ : ℝ), 0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
      D.energy (RadialCollar.correction z r a ρ) ≤ K * ρ * r ^ 2 / a)
    (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r → C.measure.real (Metric.closedBall z r) = κ * r ^ 3)
    (base : Fin m → State) (hc : CoreData S F R κ e ε base)
    (hM : 0 < M) (hcap : RadialCollar.amplitude * ρ ≤ M)
    (Rbox : ℝ) (β : V) (hβ0 : ∀ x, 0 ≤ C.eval β x) (hβle : ∀ x, C.eval β x ≤ ρ)
    (hβplateau : ∀ x ∈ Spatial.cube (Rbox - 2 * a), C.eval β x = ρ)
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) (u : Space) :
    S.density (trial S T A O F R s L Rbox M β base u) = β +
      (∑ j, if selection F s L Rbox j u then
        S.density (coreState S T A s L base j u) - coreCharge T F R s L j u else 0) +
      (∑ j, if selection F s L Rbox j u then collarCharge T F R s L j u else 0) ∧
    C.mass (S.density (trial S T A O F R s L Rbox M β base u)) = C.mass β ∧
    S.jellium (trial S T A O F R s L Rbox M β base u) β ≤
      (e + ε) * (∑ j, if selection F s L Rbox j u then
        κ * F.radius (PeriodicTrial.copyIndex m s j).1 ^ 3 else 0) + h₂ * S.gradient β +
      (h₂ * K * ρ / a + (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) *
        (∑ j, if selection F s L Rbox j u then F.radius (PeriodicTrial.copyIndex m s j).1 ^ 2 else 0) +
      h₂ * cTF * M ^ ((2 : ℝ) / 3) *
        (C.mass β - ρ * (∑ j, if selection F s L Rbox j u then
          κ * F.radius (PeriodicTrial.copyIndex m s j).1 ^ 3 else 0)) := by
  let Fu := PeriodicTrial.family F s hL hinside u
  let Ru := PeriodicTrial.representatives T F R s hL hinside u
  have hplateau : ∀ j, selection F s L Rbox j u →
      ∀ x ∈ Metric.closedBall (Fu.center j) (Fu.radius j + 2 * a), C.eval β x = ρ := by
    intro j hj x hx
    apply hβplateau x
    rw [← Lattice.eroded_cube_eq Rbox a ha.le]
    exact hj hx
  have h := SelectedConstruction.paddedTrial_bounds S D Fu Ru (fun j => selection F s L Rbox j u)
    ha hρ β hβ0 hβle hplateau O Laws hsf hh₂ hKcost hvolume
    (PeriodicTrial.cores S T A (L := L) s base u)
    (PeriodicTrial.coreData S T A F R s hL hinside base hc hpreserve u) hM hcap hβmem
  rw [trial_eq_padded S T A O F R s hL hinside]
  exact h


/-- Pointwise density formula in the exact finite double-sum form used by
periodic averaging and the product-measure integrability proof. -/
theorem density_formula (L Rbox M : ℝ) (β : V) (base : Fin m → State) (u : Space)
    (hd : S.density (trial S T A O F R s L Rbox M β base u) = β +
      (∑ j, if selection F s L Rbox j u then
        S.density (coreState S T A s L base j u) - coreCharge T F R s L j u else 0) +
      ∑ j, if selection F s L Rbox j u then collarCharge T F R s L j u else 0)
    (x : Space) :
    C.eval (S.density (trial S T A O F R s L Rbox M β base u)) x = C.eval β x +
      ∑ i, ∑ z ∈ s, Spatial.selectedCorrection (Spatial.cube Rbox) a
        (F.center i + Spatial.latticeShift L z + u) (F.radius i + 2 * a)
        (fun y => C.eval (S.density (base i) - R.core i + R.collar i)
          (y - Spatial.latticeShift L z - u)) x := by
  have hv : S.density (trial S T A O F R s L Rbox M β base u) = β +
      ∑ j, if selection F s L Rbox j u then T.map (PeriodicTrial.shift s L u j)
        (S.density (base (PeriodicTrial.copyIndex m s j).1) - R.core (PeriodicTrial.copyIndex m s j).1 +
          R.collar (PeriodicTrial.copyIndex m s j).1) else 0 := by
    rw [hd, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : selection F s L Rbox j u
    · simp only [hj, ite_true, coreState, coreCharge, collarCharge, A.density, map_add, map_sub]
    · simp only [hj, ite_false, add_zero]
  rw [hv]
  rw [map_add, Pi.add_apply, map_sum, Finset.sum_apply]
  have heval (j : Fin (Fintype.card (Fin m × s))) :
      C.eval (if selection F s L Rbox j u then T.map (PeriodicTrial.shift s L u j)
        (S.density (base (PeriodicTrial.copyIndex m s j).1) - R.core (PeriodicTrial.copyIndex m s j).1 +
          R.collar (PeriodicTrial.copyIndex m s j).1) else 0) x =
      Spatial.selectedCorrection (Spatial.cube Rbox) a
        (F.center (PeriodicTrial.copyIndex m s j).1 +
          Spatial.latticeShift L (PeriodicTrial.copyIndex m s j).2.val + u)
        (F.radius (PeriodicTrial.copyIndex m s j).1 + 2 * a)
        (fun y => C.eval (S.density (base (PeriodicTrial.copyIndex m s j).1) -
          R.core (PeriodicTrial.copyIndex m s j).1 + R.collar (PeriodicTrial.copyIndex m s j).1)
          (y - Spatial.latticeShift L (PeriodicTrial.copyIndex m s j).2.val - u)) x := by
    by_cases hj : selection F s L Rbox j u
    · simp only [hj, ite_true, T.eval, PeriodicTrial.shift, sub_add_eq_sub_sub]
      simp only [Spatial.selectedCorrection, selection] at hj ⊢
      simp only [hj, ite_true]
    · simp only [hj, ite_false, map_zero, Pi.zero_apply]
      simp only [Spatial.selectedCorrection, selection] at hj ⊢
      simp only [hj, ite_false]
  simp_rw [heval]
  congr 1
  exact PeriodicTrial.sum_copyIndex m s (fun i z =>
    Spatial.selectedCorrection (Spatial.cube Rbox) a (F.center i + Spatial.latticeShift L z + u)
      (F.radius i + 2 * a) (fun y => C.eval (S.density (base i) - R.core i + R.collar i)
        (y - Spatial.latticeShift L z - u)) x)


include hL hinside in
theorem fluid_bound (hpolar : RadialCollar.PolarLaw C.measure sf)
    (ha : 0 < a) (hρ : 0 ≤ ρ) (Rbox : ℝ) (β : V)
    (hβ0 : ∀ x, 0 ≤ C.eval β x) (hβle : ∀ x, C.eval β x ≤ ρ)
    (hβplateau : ∀ x ∈ Spatial.cube (Rbox - 2 * a), C.eval β x = ρ) (u x : Space) :
    0 ≤ C.eval (MeasurableTrial.fluid β (selection F s L Rbox)
      (coreCharge T F R s L) (collarCharge T F R s L) u) x ∧
    C.eval (MeasurableTrial.fluid β (selection F s L Rbox)
      (coreCharge T F R s L) (collarCharge T F R s L) u) x ≤ RadialCollar.amplitude * ρ := by
  let Fu := PeriodicTrial.family F s hL hinside u
  let Ru := PeriodicTrial.representatives T F R s hL hinside u
  have hplateau : ∀ j, selection F s L Rbox j u →
      ∀ x ∈ Metric.closedBall (Fu.center j) (Fu.radius j + 2 * a), C.eval β x = ρ := by
    intro j hj x hx
    apply hβplateau x
    rw [← Lattice.eroded_cube_eq Rbox a ha.le]
    exact hj hx
  exact SelectedConstruction.fluid_bound Fu Ru (fun j => selection F s L Rbox j u)
    hpolar ha hρ β hβ0 hβle hplateau x

/-- The pointwise core-plus-fluid identity, with the actual explicit fluid. -/
theorem density_core_fluid (L Rbox M : ℝ) (β : V) (base : Fin m → State) (u : Space)
    (hd : S.density (trial S T A O F R s L Rbox M β base u) = β +
      (∑ j, if selection F s L Rbox j u then
        S.density (coreState S T A s L base j u) - coreCharge T F R s L j u else 0) +
      ∑ j, if selection F s L Rbox j u then collarCharge T F R s L j u else 0)
    (x : Space) :
    C.eval (S.density (trial S T A O F R s L Rbox M β base u)) x =
      C.eval (MeasurableTrial.fluid β (selection F s L Rbox)
        (coreCharge T F R s L) (collarCharge T F R s L) u) x +
      ∑ i, ∑ z ∈ s, Spatial.selectedCorrection (Spatial.cube Rbox) a
        (F.center i + Spatial.latticeShift L z + u) (F.radius i + 2 * a)
        (fun y => C.eval (S.density (base i)) (y - Spatial.latticeShift L z - u)) x := by
  have hv : S.density (trial S T A O F R s L Rbox M β base u) =
      MeasurableTrial.fluid β (selection F s L Rbox)
        (coreCharge T F R s L) (collarCharge T F R s L) u +
      ∑ j, if selection F s L Rbox j u then S.density (coreState S T A s L base j u) else 0 := by
    rw [hd]
    have hdiff (j : Fin (Fintype.card (Fin m × s))) :
        (if selection F s L Rbox j u then S.density (coreState S T A s L base j u) -
          coreCharge T F R s L j u else 0) =
        (if selection F s L Rbox j u then S.density (coreState S T A s L base j u) else 0) -
          (if selection F s L Rbox j u then coreCharge T F R s L j u else 0) := by
      by_cases hj : selection F s L Rbox j u <;> simp only [hj, ite_true, ite_false, sub_zero]
    simp_rw [hdiff]
    simp only [MeasurableTrial.fluid, MeasurableTrial.maskedCharge, Finset.sum_sub_distrib]
    abel
  rw [hv]
  rw [map_add, Pi.add_apply, map_sum, Finset.sum_apply]
  have heval (j : Fin (Fintype.card (Fin m × s))) :
      C.eval (if selection F s L Rbox j u then S.density (coreState S T A s L base j u) else 0) x =
      Spatial.selectedCorrection (Spatial.cube Rbox) a
        (F.center (PeriodicTrial.copyIndex m s j).1 +
          Spatial.latticeShift L (PeriodicTrial.copyIndex m s j).2.val + u)
        (F.radius (PeriodicTrial.copyIndex m s j).1 + 2 * a)
        (fun y => C.eval (S.density (base (PeriodicTrial.copyIndex m s j).1))
          (y - Spatial.latticeShift L (PeriodicTrial.copyIndex m s j).2.val - u)) x := by
    by_cases hj : selection F s L Rbox j u
    · simp only [hj, ite_true, coreState, A.density, T.eval, PeriodicTrial.shift, sub_add_eq_sub_sub]
      simp only [Spatial.selectedCorrection, selection] at hj ⊢
      simp only [hj, ite_true]
    · simp only [hj, ite_false, map_zero, Pi.zero_apply]
      simp only [Spatial.selectedCorrection, selection] at hj ⊢
      simp only [hj, ite_false]
  simp_rw [heval]
  congr 1
  exact PeriodicTrial.sum_copyIndex m s (fun i z =>
    Spatial.selectedCorrection (Spatial.cube Rbox) a (F.center i + Spatial.latticeShift L z + u)
      (F.radius i + 2 * a) (fun y => C.eval (S.density (base i))
        (y - Spatial.latticeShift L z - u)) x)


include hL hinside in
/-- The measurable actual trial family with its fixed mass and upper estimate
in the double-sum selected-volume notation used for the thermodynamic limit. -/
theorem trial_double_bounds [IsFiniteMeasureOnCompacts C.measure]
    [MeasurableAdd₂ V] [MeasurableSub₂ V]
    (Laws : CoulombLaws C sf) (hsf : 0 ≤ sf) (hh₂ : 0 ≤ h₂) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hpreserve : ∀ u : Space, MeasurePreserving (fun x : Space => x - u) C.measure C.measure)
    {κ e ε M K : ℝ}
    (hKcost : ∀ (z : Space) (r a ρ : ℝ), 0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
      D.energy (RadialCollar.correction z r a ρ) ≤ K * ρ * r ^ 2 / a)
    (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r → C.measure.real (Metric.closedBall z r) = κ * r ^ 3)
    (base : Fin m → State) (hc : CoreData S F R κ e ε base)
    (hM : 0 < M) (hcap : RadialCollar.amplitude * ρ ≤ M)
    (Rbox : ℝ) (β : V) (hβ0 : ∀ x, 0 ≤ C.eval β x) (hβle : ∀ x, C.eval β x ≤ ρ)
    (hβplateau : ∀ x ∈ Spatial.cube (Rbox - 2 * a), C.eval β x = ρ)
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    Measurable (trial S T A O F R s L Rbox M β base) ∧
    ∀ u : Space,
      C.mass (S.density (trial S T A O F R s L Rbox M β base u)) = C.mass β ∧
      S.jellium (trial S T A O F R s L Rbox M β base u) β ≤
        (e + ε) * UpperCoverage.selectedSum L Rbox a s F.center F.radius
          (fun i => κ * F.radius i ^ 3) u + h₂ * S.gradient β +
        (h₂ * K * ρ / a + (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) *
          UpperCoverage.selectedSum L Rbox a s F.center F.radius (fun i => F.radius i ^ 2) u +
        h₂ * cTF * M ^ ((2 : ℝ) / 3) *
          (C.mass β - ρ * UpperCoverage.selectedSum L Rbox a s F.center F.radius
            (fun i => κ * F.radius i ^ 3) u) := by
  refine ⟨trial_measurable S T A O F R s L Rbox M β base ha.le, fun u => ?_⟩
  have h := trial_bounds S D T A O F R s hL hinside Laws hsf hh₂ ha hρ hpreserve
    hKcost hvolume base hc hM hcap Rbox β hβ0 hβle hβplateau hβmem u
  simpa only [sum_selected F s L Rbox (fun i => κ * F.radius i ^ 3) u,
    sum_selected F s L Rbox (fun i => F.radius i ^ 2) u, UpperCoverage.selectedSum] using h.2

end Jellium.PeriodicSelected
