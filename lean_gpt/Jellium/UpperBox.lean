import Jellium.UpperLaws
import Jellium.UpperDensity
import Jellium.UniformCounting

/-! Actual finite-box mixtures, followed by the volume-normalized upper bound.
All states here are the explicitly translated, selected Fock states. -/

open MeasureTheory Filter Topology

namespace Jellium.UpperPhysical

universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable [MeasurableAdd₂ V] [MeasurableSub₂ V]
variable {State : Type w} [MeasurableSpace State]
variable {C : TrialState.ChargeModel Space V} {h₂ cTF sf ρ eJ a L M ε : ℝ} {m : ℕ}
variable {S : TrialState.StateAPI C State h₂ cTF}
variable (laws : StandardLaws C S sf ρ eJ)
variable {F : UpperConstruction.BallFamily m a}
variable {Reps : UpperConstruction.LocalRepresentatives C F ρ}
variable (I : UpperDensity.Inputs C S laws.dirichlet F Reps L M ballFactor eJ ε)

noncomputable def occupied (R : ℝ) : Space → ℝ :=
  UpperCoverage.selectedSum L R a (I.shifts R) F.center F.radius (fun i => ballFactor * F.radius i ^ 3)

noncomputable def surface (R : ℝ) : Space → ℝ :=
  UpperCoverage.selectedSum L R a (I.shifts R) F.center F.radius (fun i => F.radius i ^ 2)

noncomputable def surfaceCost (K : ℝ) : ℝ :=
  h₂ * K * ρ / a + (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3

noncomputable def fluidCost : ℝ := h₂ * cTF * M ^ ((2 : ℝ) / 3)

variable {K : ℝ}
variable (hcost : ∀ (z : Space) (r a ρ : ℝ), 0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
  laws.dirichlet.energy (RadialCollar.correction z r a ρ) ≤ K * ρ * r ^ 2 / a)

include hcost in
theorem raw_trial_bounds (hsf : 0 ≤ sf) (hh₂ : 0 ≤ h₂) (R : ℝ) :
    Measurable (I.states laws.translations laws.stateTranslations laws.fock R) ∧
    ∀ u : Space,
      C.mass (S.density (I.states laws.translations laws.stateTranslations laws.fock R u)) = C.mass (I.β R) ∧
      S.jellium (I.states laws.translations laws.stateTranslations laws.fock R u) (I.β R) ≤
        (eJ + ε) * occupied laws I R u + h₂ * S.gradient (I.β R) +
        surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K * surface laws I R u +
        fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * (C.mass (I.β R) - ρ * occupied laws I R u) := by
  let : IsFiniteMeasureOnCompacts C.measure := by rw [laws.measure_eq]; infer_instance
  exact PeriodicSelected.trial_double_bounds S laws.dirichlet laws.translations laws.stateTranslations
    laws.fock F Reps (I.shifts R) I.hL I.inside laws.coulomb hsf hh₂ I.ha I.hρ
    laws.translation_preserving hcost laws.ball_volume I.base I.cores I.hM I.cap R (I.β R)
    (fun x => ((I.background R).bounds x).1) (fun x => ((I.background R).bounds x).2)
    (I.background R).plateau (I.background R).root_mem

include hcost in
theorem average_represented (hsf : 0 ≤ sf) (hh₂ : 0 < h₂) (R : ℝ) :
    ∃ Φ : State, Variational.realizes C S Φ
      (I.average laws.translations laws.stateTranslations laws.fock R) := by
  let : IsProbabilityMeasure (Lattice.shiftMeasure L) := Lattice.shiftMeasure_probability I.hL
  obtain ⟨hΓ, hraw⟩ := raw_trial_bounds laws I hcost hsf hh₂.le R
  have hJ := UpperEnergy.finite_uniform_bound
    (fun u => S.jellium (I.states laws.translations laws.stateTranslations laws.fock R u) (I.β R))
    (occupied laws I R) (surface laws I R)
    (UpperCoverage.selectedSum_abs_le L R a (I.shifts R) F.center F.radius _)
    (UpperCoverage.selectedSum_abs_le L R a (I.shifts R) F.center F.radius _)
    (fun u => (hraw u).2)
  obtain ⟨P, hP, hpotential⟩ := (I.background R).potential
  exact UpperMixture.mixture_exists C S laws.observables laws.mixtures (Lattice.shiftMeasure L)
    (I.states laws.translations laws.stateTranslations laws.fock R) (I.β R) hh₂ hΓ
    (I.joint_integrable laws.translations laws.stateTranslations laws.fock R)
    hP hpotential (fun u => (hraw u).1) hJ

include hcost in
theorem averaged_box_upper (hsf : 0 ≤ sf) (hh₂ : 0 < h₂) (hK : 0 ≤ K)
    {rmin : ℝ} (hrmin : 0 < rmin) (hr : ∀ i, rmin ≤ F.radius i)
    (R : ℝ) (hR : 2 * a ≤ R) :
    Variational.indirectEnergy C S (I.average laws.translations laws.stateTranslations laws.fock R) ≤
      (eJ + ε + surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K / (ballFactor * rmin) -
        fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ) *
          (∫ u, occupied laws I R u ∂Lattice.shiftMeasure L) +
      (fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ) * R ^ 3 +
      (h₂ * (16 * ρ * (∫ x, SmoothCube.fisherDensity I.χ x) * a)) * R ^ 2 := by
  let : IsProbabilityMeasure (Lattice.shiftMeasure L) := Lattice.shiftMeasure_probability I.hL
  obtain ⟨hΓ, hraw⟩ := raw_trial_bounds laws I hcost hsf hh₂.le R
  have hsurfaceCost : 0 ≤ surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K := by
    dsimp [surfaceCost]
    have := I.ha
    have := I.hρ
    positivity
  have hgradient : S.gradient (I.β R) ≤
      (16 * ρ * (∫ x, SmoothCube.fisherDensity I.χ x) * a) * R ^ 2 := by
    have h := (I.background R).gradient hR
    convert h using 1
    ring
  have hmass := (I.background R).mass (show 0 ≤ R by linarith [I.ha])
  have htrial (u : Space) := UpperEnergy.finite_energy_bound hh₂.le hsurfaceCost (hraw u).2
    (UpperCoverage.selected_surface_bound L R a (I.shifts R) F.center F.radius ballFactor_pos hrmin hr u)
    hgradient hmass
  obtain ⟨P, hP, hpotential⟩ := (I.background R).potential
  exact (UpperMixture.average_exists_and_upper C S laws.observables laws.mixtures
    (Lattice.shiftMeasure L) (I.states laws.translations laws.stateTranslations laws.fock R) (I.β R)
    (occupied laws I R) hh₂ hΓ (I.joint_integrable laws.translations laws.stateTranslations laws.fock R)
    hP hpotential (fun u => (hraw u).1)
    (UpperCoverage.selectedSum_integrable I.hL I.ha.le (I.shifts R) F.center F.radius _
      (fun i => (F.radius_pos i).le))
    (UpperCoverage.selectedSum_abs_le L R a (I.shifts R) F.center F.radius _) htrial
    (UpperMixture.stability C S laws.observables
      (I.average_integrable laws.translations laws.stateTranslations laws.fock R)
      (I.average_bounds laws.translations laws.stateTranslations laws.fock R))).2

include hcost in
/-- The fixed-packing energy estimate uniformly over all shifts. This is the
finite-error version of the manuscript's supremum/limsup bound. -/
theorem fixed_packing_uniform_rate (hsf : 0 ≤ sf) (hh₂ : 0 < h₂) (hK : 0 ≤ K)
    {rmin : ℝ} (hrmin : 0 < rmin) (hr : ∀ i, rmin ≤ F.radius i)
    (hcoverage : (∑ i, ballFactor * F.radius i ^ 3) / L ^ 3 ≤ 1)
    (R : ℝ) (hR : 2 * (I.radiusMax + 3 * a + L) ≤ R)
    (u : Space) (hu : u ∈ Lattice.fundamentalCube L) :
    S.jellium (I.states laws.translations laws.stateTranslations laws.fock R u) (I.β R) / R ^ 3 ≤
      ((∑ i, ballFactor * F.radius i ^ 3) / L ^ 3) * (eJ + ε) +
      (fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ) *
        (1 - (∑ i, ballFactor * F.radius i ^ 3) / L ^ 3) +
      surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K / (ballFactor * rmin) +
      (|eJ + ε + surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K / (ballFactor * rmin) -
          fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ| *
          (26 * (I.radiusMax + 3 * a + L)) +
        h₂ * (16 * ρ * (∫ x, SmoothCube.fisherDensity I.χ x) * a)) / R := by
  have hrad0 : 0 ≤ I.radiusMax := I.radiusMax_nonneg
  have hRpos : 0 < R := by linarith [I.ha, I.hL]
  have hRwidth : 2 * a ≤ R := by linarith [I.ha, I.hL]
  have hsurfaceCost : 0 ≤ surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K := by
    dsimp [surfaceCost]
    have := I.ha
    have := I.hρ
    positivity
  have hgradient : S.gradient (I.β R) ≤
      (16 * ρ * (∫ x, SmoothCube.fisherDensity I.χ x) * a) * R ^ 2 := by
    convert (I.background R).gradient hRwidth using 1
    ring
  have hmass := (I.background R).mass hRpos.le
  have htrial := UpperEnergy.finite_energy_bound hh₂.le hsurfaceCost
    ((raw_trial_bounds laws I hcost hsf hh₂.le R).2 u).2
    (UpperCoverage.selected_surface_bound L R a (I.shifts R) F.center F.radius ballFactor_pos hrmin hr u)
    hgradient hmass
  have hcount := UniformCounting.selectedSum_counting_error I.hL I.ha.le F.center F.radius
    (fun i => ballFactor * F.radius i ^ 3) I.center_bound (fun i => (F.radius_pos i).le)
    (fun i => mul_nonneg ballFactor_pos.le (pow_nonneg (F.radius_pos i).le 3))
    (fun i => by linarith [I.radius_le_max i])
    (show 0 ≤ I.radiusMax + 3 * a by linarith [I.ha]) hR hcoverage u hu
  have hbound := UpperEnergy.normalized_bound_of_counting hRpos
    (show S.jellium (I.states laws.translations laws.stateTranslations laws.fock R u) (I.β R) ≤
      (eJ + ε + surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K / (ballFactor * rmin) -
        fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ) * occupied laws I R u +
        (fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ) * R ^ 3 +
        (h₂ * (16 * ρ * (∫ x, SmoothCube.fisherDensity I.χ x) * a)) * R ^ 2 by
      nlinarith [htrial]) hcount
  have hc : 0 ≤ surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K / (ballFactor * rmin) :=
    div_nonneg hsurfaceCost (mul_pos ballFactor_pos hrmin).le
  have hct := mul_le_mul_of_nonneg_left hcoverage hc
  exact hbound.trans (by nlinarith)

include hcost in
/-- Epsilon formulation of the supremum/limsup estimate with the packing
held fixed. No averaging over the shift is needed for this energy bound. -/
theorem fixed_packing_uniform_upper (hsf : 0 ≤ sf) (hh₂ : 0 < h₂) (hK : 0 ≤ K)
    {rmin : ℝ} (hrmin : 0 < rmin) (hr : ∀ i, rmin ≤ F.radius i)
    (hcoverage : (∑ i, ballFactor * F.radius i ^ 3) / L ^ 3 ≤ 1) :
    ∀ η : ℝ, 0 < η → ∀ᶠ R in atTop, ∀ u ∈ Lattice.fundamentalCube L,
      S.jellium (I.states laws.translations laws.stateTranslations laws.fock R u) (I.β R) / R ^ 3 ≤
        ((∑ i, ballFactor * F.radius i ^ 3) / L ^ 3) * (eJ + ε) +
        (fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ) *
          (1 - (∑ i, ballFactor * F.radius i ^ 3) / L ^ 3) +
        surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K / (ballFactor * rmin) + η := by
  intro η hη
  let H := |eJ + ε + surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K / (ballFactor * rmin) -
      fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ| *
      (26 * (I.radiusMax + 3 * a + L)) +
    h₂ * (16 * ρ * (∫ x, SmoothCube.fisherDensity I.χ x) * a)
  have hlim : Tendsto (fun R : ℝ => H / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ))).const_mul H
  have hnear := (tendsto_order.1 hlim).2 η hη
  filter_upwards [eventually_ge_atTop (2 * (I.radiusMax + 3 * a + L)), hnear] with R hR herror
  intro u hu
  have hbound := fixed_packing_uniform_rate laws I hcost hsf hh₂ hK hrmin hr hcoverage R hR u hu
  change H / R < η at herror
  exact hbound.trans (by dsimp [H] at herror; linarith)

end Jellium.UpperPhysical
