import Jellium.UpperConstruction
import Jellium.MeasurableTrial
import Jellium.Lattice

/-! Fixed core states translated to a finite periodic envelope. All charges,
profiles and states at different shifts are translations of the same initial
objects. -/

open Set Finset MeasureTheory Classical
set_option maxHeartbeats 250000

namespace Jellium.PeriodicTrial

open UpperConstruction MeasurableTrial
abbrev Space := RadialCollar.Space
universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable {State : Type w} [MeasurableSpace State]
variable {C : TrialState.ChargeModel Space V} {h₂ cTF : ℝ}
variable (S : TrialState.StateAPI C State h₂ cTF)
variable (T : ChargeTranslations C) (A : StateTranslations C S T)

theorem shifted_dist (x z u : Space) : dist (x - u) z = dist x (z + u) := by
  simp only [dist_eq_norm]
  congr 1
  abel

theorem shifted_core {q : V} {z : Space} {r ρ : ℝ}
    (hq : C.eval q = RadialCollar.coreBackground z r ρ) (u : Space) :
    C.eval (T.map u q) = RadialCollar.coreBackground (z + u) r ρ := by
  funext x
  rw [T.eval, hq]
  simp only [RadialCollar.coreBackground, shifted_dist]

theorem shifted_collar {g : V} {z : Space} {r a ρ : ℝ}
    (hg : C.eval g = RadialCollar.charge z r a ρ) (u : Space) :
    C.eval (T.map u g) = RadialCollar.charge (z + u) r a ρ := by
  funext x
  rw [T.eval, hg]
  simp only [RadialCollar.charge, RadialCollar.shellLift, shifted_dist]

theorem shifted_support {Γ : State} {z : Space} {r : ℝ}
    (hs : Function.support (C.eval (S.density Γ)) ⊆ Metric.closedBall z r) (u : Space) :
    Function.support (C.eval (S.density (A.map u Γ))) ⊆ Metric.closedBall (z + u) r := by
  intro x hx
  change C.eval (S.density (A.map u Γ)) x ≠ 0 at hx
  rw [A.density, T.eval] at hx
  simpa only [Metric.mem_closedBall, shifted_dist] using hs hx

theorem shifted_radial {Γ : State} {z : Space}
    (hr : RadialCollar.RadialAbout z (C.eval (S.density Γ))) (u : Space) :
    RadialCollar.RadialAbout (z + u) (C.eval (S.density (A.map u Γ))) := by
  obtain ⟨f, hf⟩ := hr
  refine ⟨f, fun x => ?_⟩
  rw [A.density, T.eval, hf, shifted_dist]

theorem shifted_jellium (Γ : State) (q : V) (u : Space) :
    S.jellium (A.map u Γ) (T.map u q) = S.jellium Γ q := by
  simp only [TrialState.StateAPI.jellium, CoulombForm.jellium,
    A.kinetic, A.repulsion, A.density, T.coulomb]

@[irreducible] noncomputable def copyIndex (m : ℕ) (s : Finset Spatial.LatticeIndex) :
    Fin (Fintype.card (Fin m × s)) ≃ Fin m × s := (Fintype.equivFin _).symm


theorem sum_copyIndex {W : Type*} [AddCommMonoid W] (m : ℕ)
    (s : Finset Spatial.LatticeIndex) (f : Fin m → Spatial.LatticeIndex → W) :
    (∑ j, f (copyIndex m s j).1 (copyIndex m s j).2.val) = ∑ i, ∑ z ∈ s, f i z := by
  calc
    _ = ∑ iz : Fin m × s, f iz.1 iz.2.val := (copyIndex m s).sum_comp (fun iz => f iz.1 iz.2.val)
    _ = _ := by simp only [Fintype.sum_prod_type, Finset.sum_coe_sort]

variable {m : ℕ} {a ρ L : ℝ}
variable (F : BallFamily m a) (R : LocalRepresentatives C F ρ)
variable (s : Finset Spatial.LatticeIndex) (hL : 0 < L)
variable (hinside : ∀ i, Metric.closedBall (F.center i) (F.radius i + 2 * a) ⊆ Spatial.cube L)

noncomputable def index (m : ℕ) (s : Finset Spatial.LatticeIndex)
    (j : Fin (Fintype.card (Fin m × s))) : Fin m × Spatial.LatticeIndex :=
  ((copyIndex m s j).1, (copyIndex m s j).2.val)

theorem index_injective (m : ℕ) (s : Finset Spatial.LatticeIndex) :
    Function.Injective (index m s) := by
  intro i j hij
  apply (copyIndex m s).injective
  apply Prod.ext
  · exact congrArg (fun p : Fin m × Spatial.LatticeIndex => p.1) hij
  · apply Subtype.ext
    exact congrArg (fun p : Fin m × Spatial.LatticeIndex => p.2) hij

include hL hinside in
theorem family_disjoint (u : Space) :
    Pairwise fun i j : Fin (Fintype.card (Fin m × s)) =>
      Disjoint (Metric.closedBall (F.center (copyIndex m s i).1 +
        Spatial.latticeShift L (copyIndex m s i).2.val + u) (F.radius (copyIndex m s i).1 + 2 * a))
      (Metric.closedBall (F.center (copyIndex m s j).1 +
        Spatial.latticeShift L (copyIndex m s j).2.val + u) (F.radius (copyIndex m s j).1 + 2 * a)) := by
  intro i j hij
  have hp := Lattice.periodic_closedBalls_disjoint L hL F.center (fun k => F.radius k + 2 * a)
    hinside F.disjoint u
  exact @hp (index m s i) (index m s j) (fun h => hij (index_injective m s h))

noncomputable def family (u : Space) : BallFamily (Fintype.card (Fin m × s)) a where
  center j := F.center (copyIndex m s j).1 + Spatial.latticeShift L (copyIndex m s j).2.val + u
  radius j := F.radius (copyIndex m s j).1
  radius_pos j := F.radius_pos (copyIndex m s j).1
  collar_room j := F.collar_room (copyIndex m s j).1
  disjoint := family_disjoint F s hL hinside u

noncomputable def shift (L : ℝ) (u : Space) (j : Fin (Fintype.card (Fin m × s))) : Space :=
  Spatial.latticeShift L (copyIndex m s j).2.val + u

noncomputable def representatives (u : Space) : LocalRepresentatives C (family F s hL hinside u) ρ where
  core j := T.map (shift s L u j) (R.core (copyIndex m s j).1)
  collar j := T.map (shift s L u j) (R.collar (copyIndex m s j).1)
  core_eval j := by
    simpa only [family, shift, add_assoc] using shifted_core T (R.core_eval (copyIndex m s j).1)
      (shift s L u j)
  collar_eval j := by
    simpa only [family, shift, add_assoc] using shifted_collar T (R.collar_eval (copyIndex m s j).1)
      (shift s L u j)

noncomputable def cores (base : Fin m → State) (u : Space)
    (j : Fin (Fintype.card (Fin m × s))) : State :=
  A.map (shift s L u j) (base (copyIndex m s j).1)

include hL hinside in
theorem coreData {κ e ε : ℝ} (base : Fin m → State) (hc : CoreData S F R κ e ε base)
    (hpreserve : ∀ u : Space, MeasurePreserving (fun x : Space => x - u) C.measure C.measure)
    (u : Space) :
    CoreData S (family F s hL hinside u) (representatives T F R s hL hinside u) κ e ε
      (cores S T A (L := L) s base u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hint := (hpreserve (shift s L u j)).integrable_comp_of_integrable (hc.integrable (copyIndex m s j).1)
    have heq : C.eval (S.density (cores S T A (L := L) s base u j)) =
        (fun x => C.eval (S.density (base (copyIndex m s j).1)) (x - shift s L u j)) := by
      funext x
      exact (A.density _ _ ▸ T.eval _ _ x)
    rw [heq]
    exact hint
  · intro j
    simpa only [cores, family, shift, add_assoc] using
      shifted_support S T A (hc.support (copyIndex m s j).1) (shift s L u j)
  · intro j
    simpa only [cores, family, shift, add_assoc] using
      shifted_radial S T A (hc.radial (copyIndex m s j).1) (shift s L u j)
  · intro j
    change C.mass (S.density (A.map _ _)) = C.mass (T.map _ _)
    rw [A.density, T.mass, T.mass]
    exact hc.neutral _
  · intro j
    change S.jellium (A.map _ _) (T.map _ _) ≤ _
    rw [shifted_jellium S T A]
    exact hc.upper _

end Jellium.PeriodicTrial
