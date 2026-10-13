import Jellium.TrialState
import Jellium.RadialCollar
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Concrete measurable quasifree and finite Fock operations. Selection is made on
one fixed finite envelope. Unselected factors are the vacuum, so no arbitrary
choice of a state is made at each translation parameter.
-/

open Set Finset MeasureTheory

namespace Jellium.MeasurableTrial

universe u v w
abbrev Space := RadialCollar.Space
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable {State : Type w} [MeasurableSpace State]
variable (C : TrialState.ChargeModel Space V) {h₂ cTF : ℝ}
variable (S : TrialState.StateAPI C State h₂ cTF)

/-- The ordinary charge translation representation. -/
structure ChargeTranslations where
  map : Space → V →ₗ[ℝ] V
  measurable : Measurable (fun p : Space × V => map p.1 p.2)
  eval : ∀ u f x, C.eval (map u f) x = C.eval f (x - u)
  mass : ∀ u f, C.mass (map u f) = C.mass f
  coulomb : ∀ u f g, C.coulomb.form (map u f) (map u g) = C.coulomb.form f g

/-- Unitary translation of Fock states, with its usual observable laws. -/
structure StateTranslations (T : ChargeTranslations C) where
  map : Space → State → State
  measurable : Measurable (fun p : Space × State => map p.1 p.2)
  density : ∀ u Γ, S.density (map u Γ) = T.map u (S.density Γ)
  kinetic : ∀ u Γ, S.kinetic (map u Γ) = S.kinetic Γ
  repulsion : ∀ u Γ, S.repulsion (map u Γ) = S.repulsion Γ

/-- Standard explicit Fock operations. Measurability belongs to the general
operators, not to a packing-dependent trial-state existence assumption. -/
structure FockOperations where
  vacuum : State
  vacuum_density : S.density vacuum = 0
  vacuum_kinetic : S.kinetic vacuum = 0
  vacuum_repulsion : S.repulsion vacuum = 0
  quasifree : ℝ → V → State
  quasifree_measurable : ∀ M, Measurable (quasifree M)
  quasifree_laws : ∀ M p, 0 < M → S.regular p →
    (∀ x, 0 ≤ C.eval p x ∧ C.eval p x ≤ M) →
    S.density (quasifree M p) = p ∧
    S.indirect (quasifree M p) ≤ h₂ * S.gradient p +
      h₂ * cTF * M ^ ((2 : ℝ) / 3) * C.mass p
  product : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (ι → State) → State
  product_measurable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Measurable (product ι)
  product_laws : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → State),
    Pairwise (fun i j => Disjoint (Function.support (C.eval (S.density (f i))))
      (Function.support (C.eval (S.density (f j))))) →
    S.density (product ι f) = ∑ i, S.density (f i) ∧
    S.kinetic (product ι f) = ∑ i, S.kinetic (f i) ∧
    S.repulsion (product ι f) = (∑ i, S.repulsion (f i)) +
      C.coulomb.form (∑ i, S.density (f i)) (∑ i, S.density (f i)) -
      ∑ i, C.coulomb.form (S.density (f i)) (S.density (f i))

variable {C S}

namespace FockOperations
variable (O : FockOperations C S)

theorem vacuum_indirect : S.indirect O.vacuum = 0 := by
  simp [TrialState.StateAPI.indirect, CoulombForm.indirect,
    O.vacuum_density, O.vacuum_kinetic, O.vacuum_repulsion]

theorem product_indirect (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → State)
    (hdisjoint : Pairwise (fun i j =>
      Disjoint (Function.support (C.eval (S.density (f i))))
        (Function.support (C.eval (S.density (f j)))))) :
    S.indirect (O.product ι f) = ∑ i, S.indirect (f i) := by
  obtain ⟨hd, hT, hW⟩ := O.product_laws ι f hdisjoint
  simp only [TrialState.StateAPI.indirect, CoulombForm.indirect]
  rw [hd, hT, hW]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  ring

end FockOperations

variable {U : Type u} [MeasurableSpace U]
variable {n : ℕ}

noncomputable def maskedCharge (selected : Fin n → U → Prop) (f : Fin n → U → V)
    (i : Fin n) (u : U) : V := by
  classical
  exact if selected i u then f i u else 0

noncomputable def fluid (β : V) (selected : Fin n → U → Prop)
    (q g : Fin n → U → V) (u : U) : V :=
  β - ∑ i, maskedCharge selected q i u + ∑ i, maskedCharge selected g i u

noncomputable def coreFactors (O : FockOperations C S) (selected : Fin n → U → Prop)
    (cores : Fin n → U → State) (i : Fin n) (u : U) : State := by
  classical
  exact if selected i u then cores i u else O.vacuum

noncomputable def factors (O : FockOperations C S) (M : ℝ) (β : V)
    (selected : Fin n → U → Prop) (q g : Fin n → U → V)
    (cores : Fin n → U → State) (u : U) : Option (Fin n) → State :=
  fun i => i.elim (O.quasifree M (fluid β selected q g u))
    (fun j => coreFactors O selected cores j u)

noncomputable def trial (O : FockOperations C S) (M : ℝ) (β : V)
    (selected : Fin n → U → Prop) (q g : Fin n → U → V)
    (cores : Fin n → U → State) (u : U) : State :=
  O.product (Option (Fin n)) (factors O M β selected q g cores u)

omit [Module ℝ V] in
theorem maskedCharge_measurable (selected : Fin n → U → Prop) (f : Fin n → U → V)
    (hsel : ∀ i, MeasurableSet {u | selected i u})
    (hf : ∀ i, Measurable (f i)) (i : Fin n) :
    Measurable (maskedCharge selected f i) := by
  classical
  exact Measurable.ite (hsel i) (hf i) measurable_const

omit [Module ℝ V] in
theorem fluid_measurable [MeasurableAdd₂ V] [MeasurableSub₂ V] (β : V) (selected : Fin n → U → Prop) (q g : Fin n → U → V)
    (hsel : ∀ i, MeasurableSet {u | selected i u})
    (hq : ∀ i, Measurable (q i)) (hg : ∀ i, Measurable (g i)) :
    Measurable (fluid β selected q g) := by
  apply Measurable.add
  · exact measurable_const.sub (Finset.measurable_sum _
      (fun i _ => maskedCharge_measurable selected q hsel hq i))
  · exact Finset.measurable_sum _ (fun i _ => maskedCharge_measurable selected g hsel hg i)

theorem coreFactors_measurable (O : FockOperations C S) (selected : Fin n → U → Prop)
    (cores : Fin n → U → State)
    (hsel : ∀ i, MeasurableSet {u | selected i u})
    (hcores : ∀ i, Measurable (cores i)) (i : Fin n) :
    Measurable (coreFactors O selected cores i) := by
  classical
  exact Measurable.ite (hsel i) (hcores i) measurable_const

theorem trial_measurable [MeasurableAdd₂ V] [MeasurableSub₂ V] (O : FockOperations C S) (M : ℝ) (β : V)
    (selected : Fin n → U → Prop) (q g : Fin n → U → V) (cores : Fin n → U → State)
    (hsel : ∀ i, MeasurableSet {u | selected i u})
    (hq : ∀ i, Measurable (q i)) (hg : ∀ i, Measurable (g i))
    (hcores : ∀ i, Measurable (cores i)) :
    Measurable (trial O M β selected q g cores) := by
  apply (O.product_measurable (Option (Fin n))).comp
  apply measurable_pi_lambda
  intro i
  cases i with
  | none => exact (O.quasifree_measurable M).comp (fluid_measurable β selected q g hsel hq hg)
  | some i => exact coreFactors_measurable O selected cores hsel hcores i

theorem translatedCharge_measurable (T : ChargeTranslations C) (q : V)
    (shift : U → Space) (hshift : Measurable shift) :
    Measurable (fun u => T.map (shift u) q) :=
  T.measurable.comp (hshift.prodMk measurable_const)

theorem translatedState_measurable (T : ChargeTranslations C) (A : StateTranslations C S T)
    (Γ : State) (shift : U → Space) (hshift : Measurable shift) :
    Measurable (fun u => A.map (shift u) Γ) :=
  A.measurable.comp (hshift.prodMk measurable_const)


omit [MeasurableSpace U] in
theorem coreFactors_density (O : FockOperations C S) (selected : Fin n → U → Prop)
    (cores : Fin n → U → State) (i : Fin n) (u : U) :
    S.density (coreFactors O selected cores i u) =
      maskedCharge selected (fun j v => S.density (cores j v)) i u := by
  classical
  by_cases hi : selected i u <;> simp [coreFactors, maskedCharge, hi, O.vacuum_density]

omit [MeasurableSpace U] in
theorem factors_disjoint (O : FockOperations C S) {M : ℝ} (β : V)
    (selected : Fin n → U → Prop) (q g : Fin n → U → V) (cores : Fin n → U → State)
    (u : U) (A : Fin n → Set Space)
    (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (hsupport : ∀ i, Function.support (C.eval (S.density (cores i u))) ⊆ A i)
    (hzero : ∀ i, selected i u → ∀ x ∈ A i, C.eval (fluid β selected q g u) x = 0)
    (hΦ : S.density (O.quasifree M (fluid β selected q g u)) = fluid β selected q g u) :
    Pairwise fun i j =>
      Disjoint (Function.support (C.eval (S.density (factors O M β selected q g cores u i))))
        (Function.support (C.eval (S.density (factors O M β selected q g cores u j)))) := by
  classical
  have hc : ∀ i, Function.support (C.eval (S.density (coreFactors O selected cores i u))) ⊆ A i := by
    intro i x hx
    by_cases hi : selected i u
    · simpa [coreFactors, hi] using hsupport i (by simpa [coreFactors, hi] using hx)
    · simp [coreFactors, hi, O.vacuum_density] at hx
  have hf : ∀ i, Disjoint
      (Function.support (C.eval (S.density (O.quasifree M (fluid β selected q g u)))))
      (Function.support (C.eval (S.density (coreFactors O selected cores i u)))) := by
    intro i
    apply Set.disjoint_left.2
    intro x hfluid hcore
    by_cases hi : selected i u
    · exact hfluid (by rw [hΦ]; exact hzero i hi x (hc i hcore))
    · simp [coreFactors, hi, O.vacuum_density] at hcore
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j => exact hf j
  | some i =>
    cases j with
    | none => exact (hf i).symm
    | some j => exact (hA (fun h => hij (congrArg some h))).mono (hc i) (hc j)

omit [MeasurableSpace U] in
theorem trial_laws (O : FockOperations C S) {M : ℝ} (β : V)
    (selected : Fin n → U → Prop) (q g : Fin n → U → V) (cores : Fin n → U → State)
    (u : U) (hM : 0 < M) (hregular : S.regular (fluid β selected q g u))
    (hbound : ∀ x, 0 ≤ C.eval (fluid β selected q g u) x ∧
      C.eval (fluid β selected q g u) x ≤ M)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (Function.support (C.eval (S.density (factors O M β selected q g cores u i))))
        (Function.support (C.eval (S.density (factors O M β selected q g cores u j))))) :
    S.density (trial O M β selected q g cores u) = β +
      (∑ i, (maskedCharge selected (fun j v => S.density (cores j v)) i u -
        maskedCharge selected q i u)) + ∑ i, maskedCharge selected g i u ∧
    S.indirect (trial O M β selected q g cores u) =
      (∑ i, S.indirect (coreFactors O selected cores i u)) +
        S.indirect (O.quasifree M (fluid β selected q g u)) ∧
    S.indirect (O.quasifree M (fluid β selected q g u)) ≤
      h₂ * S.gradient (fluid β selected q g u) +
        h₂ * cTF * M ^ ((2 : ℝ) / 3) * C.mass (fluid β selected q g u) := by
  classical
  obtain ⟨hΦ, hΦbound⟩ := O.quasifree_laws M (fluid β selected q g u) hM hregular hbound
  obtain ⟨hd, _hT, _hW⟩ := O.product_laws (Option (Fin n))
    (factors O M β selected q g cores u) hdisjoint
  have hI := O.product_indirect (Option (Fin n))
    (factors O M β selected q g cores u) hdisjoint
  refine ⟨?_, ?_, hΦbound⟩
  · rw [trial, hd, Fintype.sum_option]
    change S.density (O.quasifree M (fluid β selected q g u)) +
      (∑ i, S.density (coreFactors O selected cores i u)) = _
    rw [hΦ]
    simp only [coreFactors_density, fluid, Finset.sum_sub_distrib]
    abel
  · rw [trial, hI, Fintype.sum_option]
    change S.indirect (O.quasifree M (fluid β selected q g u)) +
      (∑ i, S.indirect (coreFactors O selected cores i u)) = _
    ring

omit [MeasurableSpace V] [MeasurableSpace State] in
/-- Exact energy identity for a specified product state. This is also usable
for the concrete measurable operator output, not just existential witnesses. -/
theorem given_product_jellium {H ρ : ℝ} (G : TrialState.FluidGeometry C n ρ H)
    (cores : Fin n → State) (Φ Γ : State)
    (hΓd : S.density Γ = G.background +
      (∑ i, (S.density (cores i) - G.coreBackground i)) + ∑ i, G.collar i)
    (hΓenergy : S.indirect Γ = (∑ i, S.indirect (cores i)) + S.indirect Φ)
    (hsupport : ∀ i, Function.support (C.eval (S.density (cores i))) ⊆ G.core i)
    (hcoreNewton : ∀ i x, x ∉ G.core i →
      C.potential (S.density (cores i) - G.coreBackground i) x = 0)
    (hcollarNewton : ∀ i x, x ∉ G.enlarged i → C.potential (G.collar i) x = 0) :
    S.jellium Γ G.background = (∑ i, S.jellium (cores i) (G.coreBackground i)) +
      S.indirect Φ + ∑ i, C.coulomb.form (G.collar i) (G.collar i) := by
  obtain ⟨hcore, hcollar, hmixed⟩ := TrialState.support_cancellations C G
    (fun i => S.density (cores i)) hsupport hcoreNewton hcollarNewton
  let f : Fin n → V := fun i => S.density (cores i) - G.coreBackground i
  have hcharge : S.density Γ - G.background = (∑ i, f i) + ∑ i, G.collar i := by
    rw [hΓd]
    dsimp [f]
    abel
  have hproduct : S.jellium Γ G.background =
      (∑ i, S.indirect (cores i)) + S.indirect Φ +
        C.coulomb.form ((∑ i, f i) + ∑ i, G.collar i)
          ((∑ i, f i) + ∑ i, G.collar i) := by
    unfold TrialState.StateAPI.jellium
    rw [C.coulomb.jellium_eq_indirect_add_charge, hcharge]
    change S.indirect Γ + _ = _
    rw [hΓenergy]
  have hidentity := C.coulomb.core_fluid_identity Finset.univ f G.collar
    (fun i => S.indirect (cores i)) (S.indirect Φ) (S.jellium Γ G.background)
    (fun i _ j _ hij => hcore i j hij) (fun i _ j _ hij => hcollar i j hij)
    (fun i _ j _ => hmixed i j) hproduct
  have hcoreJ : ∀ i, S.indirect (cores i) + C.coulomb.form (f i) (f i) =
      S.jellium (cores i) (G.coreBackground i) := by
    intro i
    exact (C.coulomb.jellium_eq_indirect_add_charge
      (h₂ * S.kinetic (cores i)) (S.repulsion (cores i))
      (S.density (cores i)) (G.coreBackground i)).symm
  simp_rw [hcoreJ] at hidentity
  exact hidentity

end Jellium.MeasurableTrial
