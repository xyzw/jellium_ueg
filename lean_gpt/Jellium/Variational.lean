import Jellium.TrialState
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith

/-!
Constrained-search energies and continuum mixtures of actual states.
The state and Coulomb primitives come from TrialState. The infima below are
actual infima of state energies, rather than independent scalar parameters.
Stability and the usual probability-mixture law are explicit standard inputs.
-/

open MeasureTheory Set Filter Topology

namespace Jellium.Variational

universe u v w
variable {X : Type u} [MeasurableSpace X]
variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable {State : Type w}
variable (C : TrialState.ChargeModel X V) {h₂ cTF : ℝ}
variable (S : TrialState.StateAPI C State h₂ cTF)

/-- The admissible density is an almost-everywhere equality, as appropriate
for the constrained-search functional on physical densities. -/
def realizes (Γ : State) (p : X → ℝ) : Prop :=
  C.eval (S.density Γ) =ᵐ[C.measure] p

noncomputable def indirectEnergy (p : X → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ Γ : State, realizes C S Γ p ∧ e = S.indirect Γ}

noncomputable def canonicalEnergy (admissible : State → Prop) (background : V) : ℝ :=
  sInf {e : ℝ | ∃ Γ : State, admissible Γ ∧ e = S.jellium Γ background}

theorem indirectEnergy_le {p : X → ℝ} (Γ : State)
    (hΓ : realizes C S Γ p)
    (hstable : ∃ B : ℝ, ∀ Φ : State, realizes C S Φ p → B ≤ S.indirect Φ) :
    indirectEnergy C S p ≤ S.indirect Γ := by
  apply csInf_le
  · obtain ⟨B, hB⟩ := hstable
    exact ⟨B, fun e ⟨Φ, hΦ, he⟩ => he ▸ hB Φ hΦ⟩
  · exact ⟨Γ, hΓ, rfl⟩

theorem canonicalEnergy_le {admissible : State → Prop} {background : V} (Γ : State)
    (hΓ : admissible Γ)
    (hstable : ∃ B : ℝ, ∀ Φ : State, admissible Φ → B ≤ S.jellium Φ background) :
    canonicalEnergy C S admissible background ≤ S.jellium Γ background := by
  apply csInf_le
  · obtain ⟨B, hB⟩ := hstable
    exact ⟨B, fun e ⟨Φ, hΦ, he⟩ => he ▸ hB Φ hΦ⟩
  · exact ⟨Γ, hΓ, rfl⟩

theorem exists_indirect_near_inf {p : X → ℝ}
    (hne : ∃ Γ : State, realizes C S Γ p)
    (hstable : ∃ B : ℝ, ∀ Φ : State, realizes C S Φ p → B ≤ S.indirect Φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : State, realizes C S Γ p ∧ S.indirect Γ < indirectEnergy C S p + ε := by
  have hset : {e : ℝ | ∃ Γ : State, realizes C S Γ p ∧ e = S.indirect Γ}.Nonempty := by
    obtain ⟨Γ, hΓ⟩ := hne
    exact ⟨S.indirect Γ, Γ, hΓ, rfl⟩
  have hbdd : BddBelow {e : ℝ | ∃ Γ : State, realizes C S Γ p ∧ e = S.indirect Γ} := by
    obtain ⟨B, hB⟩ := hstable
    exact ⟨B, fun e ⟨Φ, hΦ, he⟩ => he ▸ hB Φ hΦ⟩
  obtain ⟨e, ⟨Γ, hΓ, he⟩, hlt⟩ :=
    (csInf_lt_iff hbdd hset).1 (show indirectEnergy C S p < indirectEnergy C S p + ε by linarith)
  exact ⟨Γ, hΓ, he ▸ hlt⟩

/-- Ordinary trace-class probability mixtures. Affinity is requested only for
linear observables. In particular neither indirect-energy affinity nor the
new upper bound is postulated. The background is fixed before averaging. -/
structure MixtureLaws [MeasurableSpace State] where
  mix : ∀ {A : Type} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (Γ : A → State) (background : V),
    AEMeasurable Γ μ →
    Integrable (fun tx : A × X => C.eval (S.density (Γ tx.1)) tx.2) (μ.prod C.measure) →
    Integrable (fun t => S.kinetic (Γ t)) μ →
    Integrable (fun t => S.repulsion (Γ t)) μ →
    Integrable (fun t => C.coulomb.form (S.density (Γ t)) background) μ →
    ∃ average : State,
      (C.eval (S.density average) =ᵐ[C.measure]
        fun x => ∫ t, C.eval (S.density (Γ t)) x ∂μ) ∧
      S.kinetic average = ∫ t, S.kinetic (Γ t) ∂μ ∧
      S.repulsion average = ∫ t, S.repulsion (Γ t) ∂μ ∧
      C.coulomb.form (S.density average) background =
        ∫ t, C.coulomb.form (S.density (Γ t)) background ∂μ

variable [MeasurableSpace State]

theorem continuum_fixed_background_affinity
    (laws : MixtureLaws C S)
    {A : Type} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (Γ : A → State) (background : V)
    (hΓ : AEMeasurable Γ μ)
    (hdensity : Integrable (fun tx : A × X => C.eval (S.density (Γ tx.1)) tx.2) (μ.prod C.measure))
    (hT : Integrable (fun t => S.kinetic (Γ t)) μ)
    (hW : Integrable (fun t => S.repulsion (Γ t)) μ)
    (hD : Integrable (fun t => C.coulomb.form (S.density (Γ t)) background) μ) :
    ∃ average : State,
      realizes C S average (fun x => ∫ t, C.eval (S.density (Γ t)) x ∂μ) ∧
      S.jellium average background = ∫ t, S.jellium (Γ t) background ∂μ := by
  obtain ⟨average, hd, hkin, hrep, hcross⟩ := laws.mix μ Γ background hΓ hdensity hT hW hD
  refine ⟨average, hd, ?_⟩
  simp only [TrialState.StateAPI.jellium, CoulombForm.jellium]
  rw [integral_add (f := fun t => h₂ * S.kinetic (Γ t) + S.repulsion (Γ t) -
      2 * C.coulomb.form (S.density (Γ t)) background)
      (g := fun _ => C.coulomb.form background background)
      (((hT.const_mul h₂).add hW).sub (hD.const_mul 2)) (integrable_const _),
    integral_sub (f := fun t => h₂ * S.kinetic (Γ t) + S.repulsion (Γ t))
      (g := fun t => 2 * C.coulomb.form (S.density (Γ t)) background)
      ((hT.const_mul h₂).add hW) (hD.const_mul 2),
    integral_add (f := fun t => h₂ * S.kinetic (Γ t)) (g := fun t => S.repulsion (Γ t))
      (hT.const_mul h₂) hW, integral_const_mul, integral_const_mul,
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hkin, hrep, hcross]

theorem averaged_variational_bound
    (laws : MixtureLaws C S)
    {A : Type} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (Γ : A → State) (background : V)
    (hΓ : AEMeasurable Γ μ)
    (hdensity : Integrable (fun tx : A × X => C.eval (S.density (Γ tx.1)) tx.2) (μ.prod C.measure))
    (hT : Integrable (fun t => S.kinetic (Γ t)) μ)
    (hW : Integrable (fun t => S.repulsion (Γ t)) μ)
    (hD : Integrable (fun t => C.coulomb.form (S.density (Γ t)) background) μ)
    (hstable : ∃ B : ℝ, ∀ Φ : State,
      realizes C S Φ (fun x => ∫ t, C.eval (S.density (Γ t)) x ∂μ) → B ≤ S.indirect Φ) :
    indirectEnergy C S (fun x => ∫ t, C.eval (S.density (Γ t)) x ∂μ) ≤
      ∫ t, S.jellium (Γ t) background ∂μ := by
  obtain ⟨average, hd, henergy⟩ :=
    continuum_fixed_background_affinity C S laws μ Γ background hΓ hdensity hT hW hD
  calc
    _ ≤ S.indirect average := indirectEnergy_le C S average hd hstable
    _ ≤ S.jellium average background := C.coulomb.indirect_le_jellium _ _ _ _
    _ = _ := henergy

/-- The thermodynamic value is defined by the normalized finite-volume
energies. Existence and shape independence of the limit are literature inputs. -/
noncomputable def thermodynamicValue (finiteVolume volume : ℕ → ℝ) : ℝ :=
  limUnder atTop (fun n => finiteVolume n / volume n)

theorem thermodynamicValue_eq {finiteVolume volume : ℕ → ℝ} {e : ℝ}
    (h : Tendsto (fun n => finiteVolume n / volume n) atTop (𝓝 e)) :
    thermodynamicValue finiteVolume volume = e := h.limUnder_eq

end Jellium.Variational
