import Jellium.UpperBox
import Jellium.LowerDensity

/-! Completion of the physical upper comparison. The packing, neutral core
states, smooth backgrounds, selected Fock family, mixture, localization and
both successive limits are connected in a single theorem. -/

open MeasureTheory Filter Topology

namespace Jellium.UpperPhysical

universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable [MeasurableAdd₂ V] [MeasurableSub₂ V]
variable {State : Type w} [MeasurableSpace State]
variable {C : TrialState.ChargeModel Space V} {h₂ cTF sf ρ eJ eU a L M ε : ℝ} {m : ℕ}
variable {S : TrialState.StateAPI C State h₂ cTF}
variable (laws : StandardLaws C S sf ρ eJ)
variable {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
variable (localization : UpperDensity.LocalizationLaws C S μ ρ eU)

include μ localization in
theorem fixed_family_comparison
    {F : UpperConstruction.BallFamily m a} {Reps : UpperConstruction.LocalRepresentatives C F ρ}
    (I : UpperDensity.Inputs C S laws.dirichlet F Reps L M ballFactor eJ ε)
    {K rmin : ℝ} (hsf : 0 ≤ sf) (hh₂ : 0 < h₂) (hK : 0 ≤ K)
    (hcost : ∀ (z : Space) (r a ρ : ℝ), 0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
      laws.dirichlet.energy (RadialCollar.correction z r a ρ) ≤ K * ρ * r ^ 2 / a)
    (hrmin : 0 < rmin) (hr : ∀ i, rmin ≤ F.radius i)
    (hcoverage : (∑ i, ballFactor * F.radius i ^ 3) / L ^ 3 ≤ 1) :
    eU ≤ ((∑ i, ballFactor * F.radius i ^ 3) / L ^ 3) * (eJ + ε) +
      (fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ) *
        (1 - (∑ i, ballFactor * F.radius i ^ 3) / L ^ 3) +
      surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K / (ballFactor * rmin) := by
  have hsurfaceCost : 0 ≤ surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K := by
    dsimp [surfaceCost]
    have := I.hρ
    have := I.ha
    positivity
  have hbulk := I.localized_lower_bound laws.translations laws.stateTranslations laws.fock μ
    localization (average_represented laws I hcost hsf hh₂)
  have hlimit := UpperCoverage.average_coverage_tendsto I.hL I.ha.le F.center F.radius
    (fun i => ballFactor * F.radius i ^ 3) I.center_bound (fun i => (F.radius_pos i).le)
  apply UpperEnergy.packing_limit_bound
    (B := h₂ * (16 * ρ * (∫ x, SmoothCube.fisherDensity I.χ x) * a))
    (densityEnergy := fun R => Variational.indirectEnergy C S
      (I.average laws.translations laws.stateTranslations laws.fock R))
    (averageTrial := fun R => Variational.indirectEnergy C S
      (I.average laws.translations laws.stateTranslations laws.fock R))
    (occupied := fun R => ∫ u, occupied laws I R u ∂Lattice.shiftMeasure L)
    (div_nonneg hsurfaceCost (mul_pos ballFactor_pos hrmin).le) hcoverage hbulk
    (Filter.Eventually.of_forall (fun _ => le_refl _)) _ hlimit
  filter_upwards [eventually_ge_atTop (2 * a)] with R hR
  exact averaged_box_upper laws I hcost hsf hh₂ hK hrmin hr R hR

include laws μ localization in
/-- The new upper inequality. Its premises are a fixed standard mollifier,
positive physical parameters, and the named general literature laws.
No trial, density-layer, coverage, or energy-comparison hypothesis remains. -/
theorem upper_comparison (χ : LowerDensity.Mollifier a)
    (hρ : 0 < ρ) (hh₂ : 0 < h₂) (hcTF : 0 ≤ cTF) (hsf : 0 ≤ sf) (ha : 0 < a) :
    eU ≤ eJ := by
  classical
  let : IsFiniteMeasureOnCompacts C.measure := by rw [laws.measure_eq]; infer_instance
  obtain ⟨K, hK, hcost⟩ := RadialCollar.exists_uniform_gradient_cost hsf laws.dirichlet.radial_formula
  let M := RadialCollar.amplitude * ρ
  have hM : 0 < M := mul_pos (lt_of_lt_of_le zero_lt_one RadialCollar.amplitude_ge_one) hρ
  let cost := surfaceCost (h₂ := h₂) (sf := sf) (ρ := ρ) (a := a) K
  have hcost0 : 0 ≤ cost := by dsimp [cost, surfaceCost]; positivity
  let K₀ := fluidCost (h₂ := h₂) (cTF := cTF) (M := M) * ρ
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀, fluidCost]; positivity
  choose β hβ using fun R => UpperBackground.exists_data C S laws.dirichlet laws.measure_eq
    laws.representations laws.bounded_potential laws.convolution hρ.le ha.le χ.nonnegative
    χ.integral_one (χ.support.trans Metric.ball_subset_closedBall) χ.sqrt_smooth R
  apply Upper.upper_le_of_trial_bounds hK₀
  intro ε hε hε1
  obtain ⟨rstar, _hrstar, hballs⟩ := laws.balls ε hε
  obtain ⟨rmin, hrmin, hroom, hstar, hsmall, ⟨p⟩⟩ :=
    Packing.exists_packing_for_error (rstar := rstar) hρ ballFactor_pos ha.le hcost0 hε hε1 laws.vitali
  let F := UpperConstruction.BallFamily.ofPacking p hrmin hroom
  obtain ⟨Reps⟩ := UpperConstruction.exists_local_representatives C laws.representations F
    laws.coulomb.polar ha hρ.le
  obtain ⟨base, hbase⟩ := UpperConstruction.exists_core_data S F Reps hballs
    (fun i => hstar.trans (p.radius_min i)) (fun i => ⟨p.particles i, p.neutral i⟩)
  let I : UpperDensity.Inputs C S laws.dirichlet F Reps p.length M ballFactor eJ ε := {
    measure_eq := laws.measure_eq
    ha := ha
    hρ := hρ.le
    hL := p.length_pos
    inside := p.collars_inside
    polar := laws.coulomb.polar
    obs := laws.observables
    base := base
    cores := hbase
    χ := χ.value
    β := β
    background := hβ
    hM := hM
    cap := le_rfl
  }
  have hcoverage := Packing.physical_coverage_bounds p ha.le
    (fun i => Domains.closedBall_volume_real (p.center i) (p.radius i)
      (lt_of_lt_of_le hrmin (p.radius_min i)).le)
  refine ⟨(∑ i, ballFactor * p.radius i ^ 3) / p.length ^ 3,
    cost / (ballFactor * rmin), hcoverage.1, hcoverage.2, hsmall, ?_⟩
  exact fixed_family_comparison laws μ localization I hsf hh₂ hK hcost hrmin p.radius_min hcoverage.2

end Jellium.UpperPhysical
