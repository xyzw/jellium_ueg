import Jellium.UpperConstruction
import Jellium.MeasurableTrial

/-! Selection of a finite ball family by an arbitrary predicate. The selected
family is explicitly reindexed, and its fluid is proved equal to the fixed
index masked sum used by the measurable Fock construction. -/

open Set Finset MeasureTheory Classical

namespace Jellium.SelectedConstruction

open UpperConstruction
universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable {C : TrialState.ChargeModel Space V}
variable {State : Type w} {h₂ cTF sf a ρ : ℝ} {n : ℕ}

noncomputable def count (sel : Fin n → Prop) : ℕ := by
  classical
  exact Fintype.card {i // sel i}

noncomputable def index (sel : Fin n → Prop) (j : Fin (count sel)) : Fin n := by
  classical
  exact ((Fintype.equivFin {i // sel i}).symm j).val

theorem index_selected (sel : Fin n → Prop) (j : Fin (count sel)) : sel (index sel j) := by
  classical
  exact ((Fintype.equivFin {i // sel i}).symm j).property

theorem index_injective (sel : Fin n → Prop) : Function.Injective (index sel) := by
  classical
  intro i j hij
  exact (Fintype.equivFin {i // sel i}).symm.injective (Subtype.ext hij)

theorem index_surjective (sel : Fin n → Prop) (i : Fin n) (hi : sel i) :
    ∃ j, index sel j = i := by
  classical
  exact ⟨(Fintype.equivFin {i // sel i}) ⟨i, hi⟩,
    congrArg Subtype.val ((Fintype.equivFin {i // sel i}).symm_apply_apply ⟨i, hi⟩)⟩

theorem sum_index {W : Type*} [AddCommMonoid W] (sel : Fin n → Prop) (f : Fin n → W) :
    (∑ j, f (index sel j)) = ∑ i, if sel i then f i else 0 := by
  classical
  change (∑ j : Fin (Fintype.card {i // sel i}),
    f (((Fintype.equivFin {i // sel i}).symm j).val)) = _
  calc
    _ = ∑ i : {i // sel i}, f i.val :=
      (Fintype.equivFin {i // sel i}).symm.sum_comp (fun i => f i.val)
    _ = _ := by
      rw [← Finset.sum_subtype (Finset.univ.filter sel) (by simp)]
      exact Finset.sum_filter _ _

noncomputable def family (F : BallFamily n a) (sel : Fin n → Prop) : BallFamily (count sel) a where
  center j := F.center (index sel j)
  radius j := F.radius (index sel j)
  radius_pos j := F.radius_pos (index sel j)
  collar_room j := F.collar_room (index sel j)
  disjoint := fun _ _ hij => F.disjoint (fun h => hij (index_injective sel h))

noncomputable def representatives (F : BallFamily n a) (R : LocalRepresentatives C F ρ)
    (sel : Fin n → Prop) : LocalRepresentatives C (family F sel) ρ where
  core j := R.core (index sel j)
  collar j := R.collar (index sel j)
  core_eval j := R.core_eval (index sel j)
  collar_eval j := R.collar_eval (index sel j)

variable (S : TrialState.StateAPI C State h₂ cTF) (D : SobolevDirichlet C S sf)
variable (F : BallFamily n a) (R : LocalRepresentatives C F ρ) (sel : Fin n → Prop)
variable (hpolar : RadialCollar.PolarLaw C.measure sf) (ha : 0 < a) (hρ : 0 ≤ ρ)
variable (β : V) (hβ0 : ∀ x, 0 ≤ C.eval β x) (hβle : ∀ x, C.eval β x ≤ ρ)
variable (hplateau : ∀ i, sel i → ∀ x ∈ Metric.closedBall (F.center i) (F.radius i + 2 * a),
  C.eval β x = ρ)

noncomputable def geometry : TrialState.FluidGeometry C (count sel) ρ RadialCollar.amplitude :=
  UpperConstruction.geometry C (family F sel) (representatives F R sel) hpolar ha hρ β hβ0 hβle
    (fun j => hplateau (index sel j) (index_selected sel j))

theorem fluid_eq_masked :
    (geometry F R sel hpolar ha hρ β hβ0 hβle hplateau).fluid =
      β - (∑ i, if sel i then R.core i else 0) + ∑ i, if sel i then R.collar i else 0 := by
  classical
  change β - (∑ j, R.core (index sel j)) + (∑ j, R.collar (index sel j)) = _
  rw [sum_index, sum_index]

include hpolar ha hρ hβ0 hβle hplateau in
theorem fluid_regular (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    S.regular (β - (∑ i, if sel i then R.core i else 0) +
      ∑ i, if sel i then R.collar i else 0) := by
  classical
  rw [← fluid_eq_masked F R sel hpolar ha hρ β hβ0 hβle hplateau]
  exact geometry_regular S D (family F sel) (representatives F R sel) hpolar ha hρ β hβ0 hβle
    (fun j => hplateau (index sel j) (index_selected sel j)) hβmem

include hpolar ha hρ hβ0 hβle hplateau in
theorem fluid_bound (x : Space) :
    0 ≤ C.eval (β - (∑ i, if sel i then R.core i else 0) +
      ∑ i, if sel i then R.collar i else 0) x ∧
    C.eval (β - (∑ i, if sel i then R.core i else 0) +
      ∑ i, if sel i then R.collar i else 0) x ≤ RadialCollar.amplitude * ρ := by
  classical
  rw [← fluid_eq_masked F R sel hpolar ha hρ β hβ0 hβle hplateau]
  exact (geometry F R sel hpolar ha hρ β hβ0 hβle hplateau).fluid_bounds hρ
    RadialCollar.amplitude_ge_one x

include hpolar ha hρ hβ0 hβle hplateau in
theorem fluid_zero (i : Fin n) (hi : sel i) (x : Space)
    (hx : x ∈ Metric.closedBall (F.center i) (F.radius i)) :
    C.eval (β - (∑ k, if sel k then R.core k else 0) +
      ∑ k, if sel k then R.collar k else 0) x = 0 := by
  classical
  rw [← fluid_eq_masked F R sel hpolar ha hρ β hβ0 hβle hplateau]
  obtain ⟨j, hj⟩ := index_surjective sel i hi
  apply (geometry F R sel hpolar ha hρ β hβ0 hβle hplateau).fluid_on_core (i := j)
  change x ∈ Metric.closedBall (F.center (index sel j)) (F.radius (index sel j))
  simpa only [hj] using hx


theorem gradient_bound {K : ℝ}
    (hKcost : ∀ (z : Space) (r a ρ : ℝ), 0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
      D.energy (RadialCollar.correction z r a ρ) ≤ K * ρ * r ^ 2 / a)
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    S.gradient (geometry F R sel hpolar ha hρ β hβ0 hβle hplateau).fluid ≤
      S.gradient β + K * ρ / a * (∑ i, if sel i then F.radius i ^ 2 else 0) := by
  classical
  unfold geometry
  rw [UpperConstruction.geometry_gradient_identity S D (family F sel)
    (representatives F R sel) hpolar ha hρ β hβ0 hβle
    (fun j => hplateau (index sel j) (index_selected sel j)) hβmem]
  apply add_le_add_right
  rw [← sum_index sel (fun i => F.radius i ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ K * ρ * F.radius (index sel j) ^ 2 / a :=
      hKcost _ _ _ _ (F.radius_pos _) ha (F.collar_room _) hρ
    _ = _ := by ring

theorem fluid_mass {κ : ℝ}
    (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r → C.measure.real (Metric.closedBall z r) = κ * r ^ 3) :
    C.mass (geometry F R sel hpolar ha hρ β hβ0 hβle hplateau).fluid =
      C.mass β - ρ * (∑ i, if sel i then κ * F.radius i ^ 3 else 0) := by
  classical
  rw [TrialState.FluidGeometry.fluid_mass, ← sum_index sel (fun i => κ * F.radius i ^ 3),
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact core_mass_formula hvolume (F.center (index sel j)) (F.radius_pos _).le ρ
    (R.core (index sel j)) (R.core_eval _)

theorem coreData {κ e ε : ℝ} (cores : Fin n → State) (hc : CoreData S F R κ e ε cores) :
    CoreData S (family F sel) (representatives F R sel) κ e ε (fun j => cores (index sel j)) where
  integrable j := hc.integrable (index sel j)
  support j := hc.support (index sel j)
  radial j := hc.radial (index sel j)
  neutral j := hc.neutral (index sel j)
  upper j := hc.upper (index sel j)

include ha hρ hβ0 hβle hplateau in
/-- Energy of any specified product with the selected cores. The hypotheses
are the product identity and the local quasifree estimate, not the resulting
trial upper bound. -/
theorem specified_product_bound [IsFiniteMeasureOnCompacts C.measure]
    (L : CoulombLaws C sf) (hsf : 0 ≤ sf) (hh₂ : 0 ≤ h₂)
    {κ e ε M K : ℝ}
    (hKcost : ∀ (z : Space) (r a ρ : ℝ), 0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
      D.energy (RadialCollar.correction z r a ρ) ≤ K * ρ * r ^ 2 / a)
    (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r → C.measure.real (Metric.closedBall z r) = κ * r ^ 3)
    (cores : Fin n → State) (hc : CoreData S F R κ e ε cores)
    (Φ Γ : State)
    (hd : S.density Γ = β +
      (∑ i, if sel i then S.density (cores i) - R.core i else 0) +
      ∑ i, if sel i then R.collar i else 0)
    (hI : S.indirect Γ = (∑ i, if sel i then S.indirect (cores i) else 0) + S.indirect Φ)
    (hΦ : S.indirect Φ ≤
      h₂ * S.gradient (geometry F R sel L.polar ha hρ β hβ0 hβle hplateau).fluid +
        h₂ * cTF * M ^ ((2 : ℝ) / 3) *
          C.mass (geometry F R sel L.polar ha hρ β hβ0 hβle hplateau).fluid)
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    C.mass (S.density Γ) = C.mass β ∧
    S.jellium Γ β ≤
      (e + ε) * (∑ i, if sel i then κ * F.radius i ^ 3 else 0) + h₂ * S.gradient β +
      (h₂ * K * ρ / a + (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) *
        (∑ i, if sel i then F.radius i ^ 2 else 0) +
      h₂ * cTF * M ^ ((2 : ℝ) / 3) *
        (C.mass β - ρ * (∑ i, if sel i then κ * F.radius i ^ 3 else 0)) := by
  classical
  let G := geometry F R sel L.polar ha hρ β hβ0 hβle hplateau
  let cores' : Fin (count sel) → State := fun j => cores (index sel j)
  have hd' : S.density Γ = G.background +
      (∑ j, (S.density (cores' j) - G.coreBackground j)) + ∑ j, G.collar j := by
    change S.density Γ = β +
      (∑ j, (S.density (cores (index sel j)) - R.core (index sel j))) +
      ∑ j, R.collar (index sel j)
    rw [sum_index sel (fun i => S.density (cores i) - R.core i), sum_index sel R.collar]
    exact hd
  have hI' : S.indirect Γ = (∑ j, S.indirect (cores' j)) + S.indirect Φ := by
    change S.indirect Γ = (∑ j, S.indirect (cores (index sel j))) + S.indirect Φ
    rw [sum_index sel (fun i => S.indirect (cores i))]
    exact hI
  have hcoreNewton : ∀ j x, x ∉ G.core j →
      C.potential (S.density (cores' j) - G.coreBackground j) x = 0 := by
    intro j
    exact core_newton L (F.center (index sel j)) (F.radius_pos _) ρ
      (S.density (cores (index sel j))) (R.core (index sel j))
      (R.core_eval _) (hc.integrable _) (hc.support _) (hc.radial _) (hc.neutral _)
  have hcollarNewton : ∀ j x, x ∉ G.enlarged j → C.potential (G.collar j) x = 0 := by
    intro j x hx
    change C.potential (R.collar (index sel j)) x = 0
    rw [L.potential_eval, R.collar_eval]
    exact RadialCollar.charge_zero_potential L.polar L.exterior _ ρ
      (F.radius_pos _) ha (F.collar_room _) x hx
  have hidentity := MeasurableTrial.given_product_jellium G cores' Φ Γ hd' hI'
    (fun j => hc.support (index sel j)) hcoreNewton hcollarNewton
  have hcorecost : (∑ j, S.jellium (cores' j) (G.coreBackground j)) ≤
      (e + ε) * (∑ i, if sel i then κ * F.radius i ^ 3 else 0) := by
    rw [← sum_index sel (fun i => κ * F.radius i ^ 3), Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hc.upper (index sel j))
  have hcollarcost : (∑ j, C.coulomb.form (G.collar j) (G.collar j)) ≤
      ((8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) *
        (∑ i, if sel i then F.radius i ^ 2 else 0) := by
    rw [← sum_index sel (fun i => F.radius i ^ 2), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    change C.coulomb.form (R.collar (index sel j)) (R.collar (index sel j)) ≤ _
    rw [L.energy_eval, R.collar_eval]
    calc
      _ ≤ (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * F.radius (index sel j) ^ 2 * a ^ 3 :=
        RadialCollar.coulomb_cost L.polar hsf L.field _ (F.radius_pos _) ha (F.collar_room _) hρ
      _ = _ := by ring
  have hmass := fluid_mass F R sel L.polar ha hρ β hβ0 hβle hplateau hvolume
  have hgrad := gradient_bound S D F R sel L.polar ha hρ β hβ0 hβle hplateau hKcost hβmem
  have hgradscaled := mul_le_mul_of_nonneg_left hgrad hh₂
  have hupper : S.jellium Γ β ≤
      (e + ε) * (∑ i, if sel i then κ * F.radius i ^ 3 else 0) +
      (h₂ * S.gradient G.fluid + h₂ * cTF * M ^ ((2 : ℝ) / 3) * C.mass G.fluid) +
      ((8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) *
        (∑ i, if sel i then F.radius i ^ 2 else 0) := by
    change S.jellium Γ G.background ≤ _
    rw [hidentity]
    linarith only [hcorecost, hΦ, hcollarcost]
  refine ⟨S.assembled_mass G cores' Γ hd' (fun j => hc.neutral (index sel j)), ?_⟩
  rw [hmass] at hupper
  calc
    S.jellium Γ β ≤ _ := hupper
    _ ≤ (e + ε) * (∑ i, if sel i then κ * F.radius i ^ 3 else 0) +
      (h₂ * (S.gradient β + K * ρ / a * (∑ i, if sel i then F.radius i ^ 2 else 0)) +
        h₂ * cTF * M ^ ((2 : ℝ) / 3) *
          (C.mass β - ρ * (∑ i, if sel i then κ * F.radius i ^ 3 else 0))) +
      ((8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) *
        (∑ i, if sel i then F.radius i ^ 2 else 0) := by linarith only [hgradscaled]
    _ = _ := by ring


section ConcreteProduct
variable [MeasurableSpace V] [MeasurableSpace State]
variable (O : MeasurableTrial.FockOperations C S)

noncomputable def paddedTrial (M : ℝ) (cores : Fin n → State) : State :=
  MeasurableTrial.trial O M β (fun i (_ : Unit) => sel i)
    (fun i _ => R.core i) (fun i _ => R.collar i) (fun i _ => cores i) ()

include ha hρ hβ0 hβle hplateau in
/-- Exact density of the selected product, independent of energy estimates. -/
theorem paddedTrial_density (hpolar : RadialCollar.PolarLaw C.measure sf)
    {M : ℝ} (cores : Fin n → State)
    (hsupport : ∀ i, Function.support (C.eval (S.density (cores i))) ⊆
      Metric.closedBall (F.center i) (F.radius i))
    (hM : 0 < M) (hcap : RadialCollar.amplitude * ρ ≤ M)
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    S.density (paddedTrial S F R sel β O M cores) = β +
      (∑ i, if sel i then S.density (cores i) - R.core i else 0) +
        ∑ i, if sel i then R.collar i else 0 := by
  let p := β - (∑ i, if sel i then R.core i else 0) + ∑ i, if sel i then R.collar i else 0
  have hpreg : S.regular p := fluid_regular S D F R sel hpolar ha hρ β hβ0 hβle hplateau hβmem
  have hpbounds : ∀ x, 0 ≤ C.eval p x ∧ C.eval p x ≤ M := by
    intro x
    have h := fluid_bound F R sel hpolar ha hρ β hβ0 hβle hplateau x
    exact ⟨h.1, le_trans h.2 hcap⟩
  have hΦ := O.quasifree_laws M p hM hpreg hpbounds
  have hcorepair : Pairwise fun i j => Disjoint
      (Metric.closedBall (F.center i) (F.radius i)) (Metric.closedBall (F.center j) (F.radius j)) := by
    intro i j hij
    exact (F.disjoint hij).mono
      (Metric.closedBall_subset_closedBall (by linarith))
      (Metric.closedBall_subset_closedBall (by linarith))
  have hdisjoint := MeasurableTrial.factors_disjoint O β (fun i (_ : Unit) => sel i)
    (fun i _ => R.core i) (fun i _ => R.collar i) (fun i _ => cores i) ()
    (fun i => Metric.closedBall (F.center i) (F.radius i)) hcorepair hsupport
    (fun i hi x hx => fluid_zero F R sel hpolar ha hρ β hβ0 hβle hplateau i hi x hx) hΦ.1
  obtain ⟨hd, _hI, _hΦbound⟩ := MeasurableTrial.trial_laws O β (fun i (_ : Unit) => sel i)
    (fun i _ => R.core i) (fun i _ => R.collar i) (fun i _ => cores i) () hM hpreg hpbounds hdisjoint
  have hdiff (i : Fin n) :
      MeasurableTrial.maskedCharge (fun i (_ : Unit) => sel i) (fun i _ => S.density (cores i)) i () -
        MeasurableTrial.maskedCharge (fun i (_ : Unit) => sel i) (fun i _ => R.core i) i () =
      if sel i then S.density (cores i) - R.core i else 0 := by
    by_cases hi : sel i <;> simp [MeasurableTrial.maskedCharge, hi]
  simp_rw [hdiff] at hd
  change S.density (paddedTrial S F R sel β O M cores) = _ at hd
  exact hd

include ha hρ hβ0 hβle hplateau in
/-- The specified finite product, with vacuum in every unselected slot, has
the density, mean mass and upper estimate required for shift averaging. -/
theorem paddedTrial_bounds [IsFiniteMeasureOnCompacts C.measure]
    (L : CoulombLaws C sf) (hsf : 0 ≤ sf) (hh₂ : 0 ≤ h₂)
    {κ e ε M K : ℝ}
    (hKcost : ∀ (z : Space) (r a ρ : ℝ), 0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
      D.energy (RadialCollar.correction z r a ρ) ≤ K * ρ * r ^ 2 / a)
    (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r → C.measure.real (Metric.closedBall z r) = κ * r ^ 3)
    (cores : Fin n → State) (hc : CoreData S F R κ e ε cores)
    (hM : 0 < M) (hcap : RadialCollar.amplitude * ρ ≤ M)
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    S.density (paddedTrial S F R sel β O M cores) = β +
      (∑ i, if sel i then S.density (cores i) - R.core i else 0) +
        (∑ i, if sel i then R.collar i else 0) ∧
    C.mass (S.density (paddedTrial S F R sel β O M cores)) = C.mass β ∧
    S.jellium (paddedTrial S F R sel β O M cores) β ≤
      (e + ε) * (∑ i, if sel i then κ * F.radius i ^ 3 else 0) + h₂ * S.gradient β +
      (h₂ * K * ρ / a + (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) *
        (∑ i, if sel i then F.radius i ^ 2 else 0) +
      h₂ * cTF * M ^ ((2 : ℝ) / 3) *
        (C.mass β - ρ * (∑ i, if sel i then κ * F.radius i ^ 3 else 0)) := by
  let p := β - (∑ i, if sel i then R.core i else 0) + ∑ i, if sel i then R.collar i else 0
  have hpreg : S.regular p := fluid_regular S D F R sel L.polar ha hρ β hβ0 hβle hplateau hβmem
  have hpbounds : ∀ x, 0 ≤ C.eval p x ∧ C.eval p x ≤ M := by
    intro x
    have h := fluid_bound F R sel L.polar ha hρ β hβ0 hβle hplateau x
    exact ⟨h.1, le_trans h.2 hcap⟩
  have hΦ := O.quasifree_laws M p hM hpreg hpbounds
  have hcorepair : Pairwise fun i j => Disjoint
      (Metric.closedBall (F.center i) (F.radius i)) (Metric.closedBall (F.center j) (F.radius j)) := by
    intro i j hij
    exact (F.disjoint hij).mono
      (Metric.closedBall_subset_closedBall (by linarith))
      (Metric.closedBall_subset_closedBall (by linarith))
  have hdisjoint := MeasurableTrial.factors_disjoint O β (fun i (_ : Unit) => sel i)
    (fun i _ => R.core i) (fun i _ => R.collar i) (fun i _ => cores i) ()
    (fun i => Metric.closedBall (F.center i) (F.radius i)) hcorepair hc.support
    (fun i hi x hx => fluid_zero F R sel L.polar ha hρ β hβ0 hβle hplateau i hi x hx) hΦ.1
  obtain ⟨hd, hI, hΦbound⟩ := MeasurableTrial.trial_laws O β (fun i (_ : Unit) => sel i)
    (fun i _ => R.core i) (fun i _ => R.collar i) (fun i _ => cores i) () hM hpreg hpbounds hdisjoint
  have hdiff (i : Fin n) :
      MeasurableTrial.maskedCharge (fun i (_ : Unit) => sel i) (fun i _ => S.density (cores i)) i () -
        MeasurableTrial.maskedCharge (fun i (_ : Unit) => sel i) (fun i _ => R.core i) i () =
      if sel i then S.density (cores i) - R.core i else 0 := by
    by_cases hi : sel i <;> simp [MeasurableTrial.maskedCharge, hi]
  simp_rw [hdiff] at hd
  change S.density (paddedTrial S F R sel β O M cores) = _ at hd
  have henergy (i : Fin n) :
      S.indirect (MeasurableTrial.coreFactors O (fun i (_ : Unit) => sel i)
        (fun i _ => cores i) i ()) = if sel i then S.indirect (cores i) else 0 := by
    by_cases hi : sel i <;> simp [MeasurableTrial.coreFactors, hi, O.vacuum_indirect]
  simp_rw [henergy] at hI
  have hp : (geometry F R sel L.polar ha hρ β hβ0 hβle hplateau).fluid = p :=
    fluid_eq_masked F R sel L.polar ha hρ β hβ0 hβle hplateau
  have hΦ' : S.indirect (O.quasifree M p) ≤
      h₂ * S.gradient (geometry F R sel L.polar ha hρ β hβ0 hβle hplateau).fluid +
        h₂ * cTF * M ^ ((2 : ℝ) / 3) *
          C.mass (geometry F R sel L.polar ha hρ β hβ0 hβle hplateau).fluid := by
    rw [hp]
    exact hΦbound
  exact ⟨hd, specified_product_bound S D F R sel ha hρ β hβ0 hβle hplateau
    L hsf hh₂ hKcost hvolume cores hc (O.quasifree M p)
    (paddedTrial S F R sel β O M cores) hd hI hΦ' hβmem⟩

end ConcreteProduct

end Jellium.SelectedConstruction
