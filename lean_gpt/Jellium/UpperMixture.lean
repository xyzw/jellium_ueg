import Jellium.UpperEnergy
import Jellium.MixtureIntegrability
import Jellium.PotentialBound

/-! The finite periodic state's observables are integrable and can be mixed.
Only the usual positivity, measurability and Lieb--Oxford facts are inputs.
The finite Jellium estimate supplies the needed kinetic and repulsion bounds. -/

open MeasureTheory Set

namespace Jellium.UpperMixture

universe u v w
variable {X : Type u} [MeasurableSpace X]
variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable {State : Type w} [MeasurableSpace State]
variable (C : TrialState.ChargeModel X V) {h₂ cTF : ℝ}
variable (S : TrialState.StateAPI C State h₂ cTF)

/-- General finite-energy Fock observable laws, independent of our trial
family. The LO input is stated for an arbitrary bounded integrable density. -/
structure ObservableLaws where
  density_nonnegative : ∀ Γ x, 0 ≤ C.eval (S.density Γ) x
  density_integrable : ∀ Γ, Integrable (C.eval (S.density Γ)) C.measure
  kinetic_nonnegative : ∀ Γ, 0 ≤ S.kinetic Γ
  repulsion_nonnegative : ∀ Γ, 0 ≤ S.repulsion Γ
  kinetic_measurable : Measurable S.kinetic
  repulsion_measurable : Measurable S.repulsion
  cross_measurable : ∀ β, Measurable (fun Γ => C.coulomb.form (S.density Γ) β)
  lo_constant : ℝ
  lieb_oxford : ∀ Γ p M, Variational.realizes C S Γ p → Integrable p C.measure →
    (∀ x, 0 ≤ p x ∧ p x ≤ M) →
    -lo_constant * M ^ ((1 : ℝ) / 3) * (∫ x, p x ∂C.measure) ≤ S.indirect Γ

theorem stability (laws : ObservableLaws C S) {p : X → ℝ} {M : ℝ}
    (hp : Integrable p C.measure) (hb : ∀ x, 0 ≤ p x ∧ p x ≤ M) :
    ∃ B : ℝ, ∀ Γ, Variational.realizes C S Γ p → B ≤ S.indirect Γ :=
  ⟨_, fun Γ hΓ => laws.lieb_oxford Γ p M hΓ hp hb⟩

theorem mixture_exists
    (obs : ObservableLaws C S) (mix : Variational.MixtureLaws C S)
    {U : Type} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (Γ : U → State) (β : V) {P N Jmax : ℝ} (hh₂ : 0 < h₂)
    (hΓ : Measurable Γ)
    (hdensity : Integrable (fun ux : U × X => C.eval (S.density (Γ ux.1)) ux.2)
      (μ.prod C.measure))
    (hP : 0 ≤ P) (hpotential : ∀ x, |C.potential β x| ≤ P)
    (hmass : ∀ u, C.mass (S.density (Γ u)) = N)
    (hJ : ∀ u, S.jellium (Γ u) β ≤ Jmax) :
    ∃ Φ : State, Variational.realizes C S Φ
      (fun x => ∫ u, C.eval (S.density (Γ u)) x ∂μ) := by
  have hcross (u : U) : |C.coulomb.form (S.density (Γ u)) β| ≤ (P / 2) * N := by
    simpa only [hmass u] using TrialState.mixed_coulomb_abs_le_mass C _ β hP hpotential
      (obs.density_integrable (Γ u)) (obs.density_nonnegative (Γ u))
  obtain ⟨hT, hW, hD⟩ := Variational.mixture_observables_integrable μ
    (fun u => S.kinetic (Γ u)) (fun u => S.repulsion (Γ u))
    (fun u => C.coulomb.form (S.density (Γ u)) β) hh₂
    (obs.kinetic_measurable.comp hΓ).aemeasurable
    (obs.repulsion_measurable.comp hΓ).aemeasurable
    ((obs.cross_measurable β).comp hΓ).aemeasurable
    (Filter.Eventually.of_forall (fun u => obs.kinetic_nonnegative (Γ u)))
    (Filter.Eventually.of_forall (fun u => obs.repulsion_nonnegative (Γ u)))
    (Filter.Eventually.of_forall hcross) (Filter.Eventually.of_forall hJ)
  obtain ⟨Φ, hΦ, _⟩ := Variational.continuum_fixed_background_affinity C S mix μ Γ β
    hΓ.aemeasurable hdensity hT hW hD
  exact ⟨Φ, hΦ⟩

theorem average_exists_and_upper
    (obs : ObservableLaws C S) (mix : Variational.MixtureLaws C S)
    {U : Type} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (Γ : U → State) (β : V) (occupied : U → ℝ)
    {R e ε K c B P N Q : ℝ} (hh₂ : 0 < h₂)
    (hΓ : Measurable Γ)
    (hdensity : Integrable (fun ux : U × X => C.eval (S.density (Γ ux.1)) ux.2)
      (μ.prod C.measure))
    (hP : 0 ≤ P) (hpotential : ∀ x, |C.potential β x| ≤ P)
    (hmass : ∀ u, C.mass (S.density (Γ u)) = N)
    (hoccupied : Integrable occupied μ) (hQ : ∀ u, |occupied u| ≤ Q)
    (htrial : ∀ u, S.jellium (Γ u) β ≤ (e + ε) * occupied u +
      K * (R ^ 3 - occupied u) + c * occupied u + B * R ^ 2)
    (hstable : ∃ b : ℝ, ∀ Φ : State,
      Variational.realizes C S Φ (fun x => ∫ u, C.eval (S.density (Γ u)) x ∂μ) →
      b ≤ S.indirect Φ) :
    (∃ Φ : State, Variational.realizes C S Φ
      (fun x => ∫ u, C.eval (S.density (Γ u)) x ∂μ)) ∧
    Variational.indirectEnergy C S (fun x => ∫ u, C.eval (S.density (Γ u)) x ∂μ) ≤
      (e + ε + c - K) * (∫ u, occupied u ∂μ) + K * R ^ 3 + B * R ^ 2 := by
  let Jmax := |e + ε + c - K| * Q + K * R ^ 3 + B * R ^ 2
  have hJ : ∀ u, S.jellium (Γ u) β ≤ Jmax := by
    intro u
    have hprod : (e + ε + c - K) * occupied u ≤ |e + ε + c - K| * Q := by
      calc
        _ ≤ |(e + ε + c - K) * occupied u| := le_abs_self _
        _ = |e + ε + c - K| * |occupied u| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hQ u) (abs_nonneg _)
    dsimp [Jmax]
    nlinarith [htrial u]
  have hcross (u : U) : |C.coulomb.form (S.density (Γ u)) β| ≤ (P / 2) * N := by
    simpa only [hmass u] using TrialState.mixed_coulomb_abs_le_mass C _ β hP hpotential
      (obs.density_integrable (Γ u)) (obs.density_nonnegative (Γ u))
  obtain ⟨hT, hW, hD⟩ := Variational.mixture_observables_integrable μ
    (fun u => S.kinetic (Γ u)) (fun u => S.repulsion (Γ u))
    (fun u => C.coulomb.form (S.density (Γ u)) β) hh₂
    (obs.kinetic_measurable.comp hΓ).aemeasurable
    (obs.repulsion_measurable.comp hΓ).aemeasurable
    ((obs.cross_measurable β).comp hΓ).aemeasurable
    (Filter.Eventually.of_forall (fun u => obs.kinetic_nonnegative (Γ u)))
    (Filter.Eventually.of_forall (fun u => obs.repulsion_nonnegative (Γ u)))
    (Filter.Eventually.of_forall hcross)
    (Filter.Eventually.of_forall hJ)
  have hjint : Integrable (fun u => S.jellium (Γ u) β) μ := by
    exact (((hT.const_mul h₂).add hW).sub (hD.const_mul 2)).add (integrable_const _)
  constructor
  · obtain ⟨Φ, hΦ, _⟩ := Variational.continuum_fixed_background_affinity C S mix μ Γ β
      hΓ.aemeasurable hdensity hT hW hD
    exact ⟨Φ, hΦ⟩
  · exact (Variational.averaged_variational_bound C S mix μ Γ β hΓ.aemeasurable
      hdensity hT hW hD hstable).trans
      (UpperEnergy.average_trial_bound μ _ occupied hjint hoccupied htrial)

end Jellium.UpperMixture
