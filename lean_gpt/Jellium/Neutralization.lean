import Jellium.NeutralizationElectrostatics
import Jellium.NeutralizationGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Canonical completion of a charged ball by an annulus.
The input laws are the Onsager/capacity inequality and the usual iid sampling
and disjoint radial orbital construction. They do not include a canonical
completion bound, a grand-canonical limit, or either energy comparison. -/

open MeasureTheory Set

namespace Jellium.Neutralization

open Domains RadialShells

/-- Retaining the positive capacity term in Onsager's inequality forces the
charge of every state with extensive energy to have surface order. -/
theorem charge_bound (R N E a c b C : ℝ)
    (hR : 1 ≤ R) (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hupper : E ≤ C * R ^ 3)
    (hlower : (N - b * R ^ 3) ^ 2 / (2 * (R + a)) - c * N ≤ E) :
    |N - b * R ^ 3| ≤ (2 * (1 + a) * (C + c * b + c) + 1) * R ^ 2 := by
  have hR0 : 0 < R := by linarith
  let q := N - b * R ^ 3
  let x := |q| / R ^ 2
  let A := 2 * (1 + a) * (C + c * b)
  let B := 2 * (1 + a) * c
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hx : 0 ≤ x := div_nonneg (abs_nonneg _) (sq_nonneg R)
  have hN : N ≤ |q| + b * R ^ 3 := by dsimp [q]; linarith [le_abs_self (N - b * R ^ 3)]
  have he : q ^ 2 ≤ 2 * (R + a) * ((C + c * b) * R ^ 3 + c * |q|) := by
    have he' : q ^ 2 / (2 * (R + a)) ≤ (C + c * b) * R ^ 3 + c * |q| := by
      have := mul_le_mul_of_nonneg_left hN hc
      dsimp [q] at *
      nlinarith only [hlower, hupper, this]
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2 * (R + a))).1 he'
  have hRa : R + a ≤ (1 + a) * R := by nlinarith
  have hpoly : q ^ 2 ≤ A * R ^ 4 + B * |q| * R := by
    have hm := mul_le_mul_of_nonneg_right hRa
      (show 0 ≤ 2 * ((C + c * b) * R ^ 3 + c * |q|) by positivity)
    dsimp [A, B]
    nlinarith only [he, hm]
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have hpoly' : q ^ 2 ≤ A * R ^ 4 + B * |q| * R ^ 2 := by
    have := mul_le_mul_of_nonneg_left hR2 (mul_nonneg hB (abs_nonneg q))
    linarith only [hpoly, this]
  have hqx : |q| = x * R ^ 2 := by dsimp [x]; field_simp
  have hsq : x ^ 2 ≤ A + B * x := by
    have hq2 : q ^ 2 = x ^ 2 * R ^ 4 := by
      rw [← sq_abs, hqx]
      ring
    rw [hq2, hqx] at hpoly'
    have hh : (x ^ 2 - (A + B * x)) * R ^ 4 ≤ 0 := by nlinarith only [hpoly']
    have := nonpos_of_mul_nonpos_left hh (by positivity : 0 < R ^ 4)
    linarith
  have hxbound : x ≤ A + B + 1 := by
    by_contra hn
    have hlarge : A + B + 1 < x := lt_of_not_ge hn
    have hxx : 0 < (x - 1) * (x - B) := mul_pos (by linarith) (by linarith)
    nlinarith only [hsq, hxx, hlarge]
  have := mul_le_mul_of_nonneg_right hxbound (sq_nonneg R)
  rw [← hqx] at this
  dsimp [q, A, B] at this
  nlinarith only [this]

/-- An ordinary iid point sample, followed by LN's disjoint radial orbitals.
The classical expectation includes the omitted diagonal self interaction.
The penalty mean is the elementary iid pair integral for the integrable
short-distance kinetic penalty. The inequalities are local orbital estimates,
valid for any bounded annular sampling density. -/
structure OrbitalSample {State : Type*}
    (energy : ℝ → State → ℝ) (confined : ℝ → ℕ → State → Prop)
    (R S : ℝ) (N P : ℕ) (Γ : State) (correction densityBound c : ℝ) where
  measure : Measure (Fin P → Space)
  probability : IsProbabilityMeasure measure
  realize : (Fin P → Space) → State
  classical : (Fin P → Space) → ℝ
  penalty : (Fin P → Space) → ℝ
  classical_integrable : Integrable classical measure
  penalty_integrable : Integrable penalty measure
  omittedSelf : ℝ
  omittedSelf_nonnegative : 0 ≤ omittedSelf
  classical_mean : (∫ x, classical x ∂measure) = correction - omittedSelf / P
  penalty_mean : (∫ x, penalty x ∂measure) ≤ c * densityBound * P
  canonical : ∀ᵐ x ∂measure, confined S (N + P) (realize x)
  orbital_energy : ∀ᵐ x ∂measure,
    energy S (realize x) ≤ energy R Γ + classical x + c * P + penalty x

/-- The penalized configuration is selected at or below its exact mean, as
in `completion_penalized_configuration`. The omitted particle diagonal is
retained and no positive error is introduced by the selection. -/
theorem select_orbitals {State : Type*}
    {energy : ℝ → State → ℝ} {confined : ℝ → ℕ → State → Prop}
    {R S : ℝ} {N P : ℕ} {Γ : State} {correction d c : ℝ}
    (sample : OrbitalSample energy confined R S N P Γ correction d c) :
    ∃ Ψ, confined S (N + P) Ψ ∧
      energy S Ψ ≤ energy R Γ + correction + c * (1 + d) * P -
        sample.omittedSelf / P := by
  let _ : IsProbabilityMeasure sample.measure := sample.probability
  let f := fun x => sample.classical x + sample.penalty x
  have hi : Integrable f sample.measure := sample.classical_integrable.add sample.penalty_integrable
  have hm : (∫ x, f x ∂sample.measure) ≤
      correction + c * d * P - sample.omittedSelf / P := by
    rw [integral_add sample.classical_integrable sample.penalty_integrable,
      sample.classical_mean]
    linarith [sample.penalty_mean]
  have hex : ∃ x, confined S (N + P) (sample.realize x) ∧
      energy S (sample.realize x) ≤ energy R Γ + sample.classical x + c * P + sample.penalty x ∧
      f x ≤ ∫ y, f y ∂sample.measure := by
    by_contra hn
    have hstrict : ∀ᵐ x ∂sample.measure,
        (∫ y, f y ∂sample.measure) < f x := by
      filter_upwards [sample.canonical, sample.orbital_energy] with x hc he
      exact lt_of_not_ge (fun hf => hn ⟨x, hc, he, hf⟩)
    have hequal : (fun _ => ∫ y, f y ∂sample.measure) =ᵐ[sample.measure] f := by
      apply (integral_eq_iff_of_ae_le (integrable_const _) hi (hstrict.mono fun _ h => h.le)).1
      simp only [integral_const, probReal_univ, one_smul]
    obtain ⟨x, hx, he⟩ := (hstrict.and hequal).exists
    exact (ne_of_lt hx) he
  obtain ⟨x, hc, he, hf⟩ := hex
  refine ⟨sample.realize x, hc, ?_⟩
  dsimp [f] at hf
  nlinarith

noncomputable def trimmedVolume (R S : ℝ) : ℝ :=
  ballVolume (S - 1) - ballVolume (R + 1)

noncomputable def shellCharge (ρ R S : ℝ) (P : ℕ) : ℝ → ℝ :=
  fun t => ((P : ℝ) / trimmedVolume R S) * layer (R + 1) (S - 1) t - ρ * layer R S t

/-- The compensating charge is supported in the actual completion annulus. -/
theorem shellCharge_support (ρ R S : ℝ) (P : ℕ) :
    ∀ s, s ∉ Icc R S → shellCharge ρ R S P s = 0 := by
  intro s hs
  have htrim : s ∉ Icc (R + 1) (S - 1) := by
    intro ht
    exact hs ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp [shellCharge, layer, hs, htrim]

theorem layer_mass_volume (a b : ℝ) : layerMass a b = ballVolume b - ballVolume a := by
  unfold layerMass ballVolume
  ring

theorem layer_measurable (a b : ℝ) : Measurable (layer a b) := by
  unfold layer
  exact (by fun_prop : Measurable (fun s : ℝ => 4 * Real.pi * s ^ 2)).indicator measurableSet_Icc

theorem shellCharge_properties {ρ R H L : ℝ} {N : ℕ}
    (hρ : 0 < ρ) (hR : 1 ≤ R)
    (g : NeutralizationGeometry.PreparedAnnulus ρ R H L N) :
    Measurable (shellCharge ρ R g.radius g.particles) ∧
    Integrable (shellCharge ρ R g.radius g.particles) ∧
    (∀ s, s ∉ Icc R (R + H) → shellCharge ρ R g.radius g.particles s = 0) ∧
    (∫ s, shellCharge ρ R g.radius g.particles s = -((N : ℝ) - ρ * ballVolume R)) ∧
    (∫ s, |shellCharge ρ R g.radius g.particles s| ≤ (2 * L) * R ^ 2) := by
  have hR0 : 0 < R := by linarith
  let η := (g.particles : ℝ) / trimmedVolume R g.radius
  have htrim : 0 < trimmedVolume R g.radius :=
    lt_of_lt_of_le (by have := NeutralizationGeometry.ballFactor_pos; positivity) g.trimmed_lower
  have hη : 0 ≤ η := div_nonneg (Nat.cast_nonneg _) htrim.le
  have hi : Integrable (shellCharge ρ R g.radius g.particles) :=
    ((layer_integrable (R + 1) (g.radius - 1)).const_mul _).sub
      ((layer_integrable R g.radius).const_mul _)
  have hmassp : η * layerMass (R + 1) (g.radius - 1) = g.particles := by
    rw [layer_mass_volume]
    change ((g.particles : ℝ) / trimmedVolume R g.radius) * trimmedVolume R g.radius = _
    exact div_mul_cancel₀ _ (ne_of_gt htrim)
  refine ⟨((layer_measurable (R + 1) (g.radius - 1)).const_mul _).sub
    ((layer_measurable R g.radius).const_mul _), hi, ?_, ?_, ?_⟩
  · intro s hs
    have hs₁ : s ∉ Icc (R + 1) (g.radius - 1) := by
      intro ht
      exact hs ⟨by linarith [ht.1], by linarith [ht.2, g.radius_upper]⟩
    have hs₂ : s ∉ Icc R g.radius := by
      intro ht
      exact hs ⟨ht.1, ht.2.trans g.radius_upper⟩
    simp [shellCharge, layer, hs₁, hs₂]
  · unfold shellCharge
    rw [integral_sub ((layer_integrable _ _).const_mul _)
      ((layer_integrable _ _).const_mul _), integral_const_mul, integral_const_mul,
      layer_integral _ _ (by linarith [g.radius_lower]),
      layer_integral _ _ (by linarith [g.radius_lower])]
    change η * layerMass (R + 1) (g.radius - 1) - _ = _
    rw [hmassp, layer_mass_volume]
    have hcount : (g.particles : ℝ) + N = g.total := by exact_mod_cast g.count
    linarith [g.neutral]
  · calc
      _ ≤ ∫ s, η * layer (R + 1) (g.radius - 1) s + ρ * layer R g.radius s := by
        apply integral_mono hi.abs (((layer_integrable _ _).const_mul _).add
          ((layer_integrable _ _).const_mul _))
        intro s
        change |η * layer (R + 1) (g.radius - 1) s - ρ * layer R g.radius s| ≤ _
        calc
          _ ≤ |η * layer (R + 1) (g.radius - 1) s| + |ρ * layer R g.radius s| := abs_sub _ _
          _ = _ := by
            rw [abs_of_nonneg (mul_nonneg hη (layer_nonnegative _ _ _)),
              abs_of_nonneg (mul_nonneg hρ.le (layer_nonnegative _ _ _))]
            rfl
      _ = (g.particles : ℝ) + ρ * (ballVolume g.radius - ballVolume R) := by
        rw [integral_add ((layer_integrable _ _).const_mul _)
          ((layer_integrable _ _).const_mul _), integral_const_mul, integral_const_mul,
          layer_integral _ _ (by linarith [g.radius_lower]),
          layer_integral _ _ (by linarith [g.radius_lower]), hmassp, layer_mass_volume]
      _ ≤ (2 * L) * R ^ 2 := by linarith [g.particles_le, g.background_le]

/-- The general analytic and Fock-space inputs. `sample` is the ordinary iid
annular sampler and LN local radial-orbital estimate at arbitrary particle
number and annular width. The total classical charge correction is an exact
expectation, not a bound. All cancellation, count choices, averaging and the
surface-order conclusion are derived below. -/
structure StandardLaws {State : Type*}
    (energy : ℝ → State → ℝ) (confined : ℝ → ℕ → State → Prop) (ρ : ℝ) where
  smearRadius : ℝ
  smearRadius_nonnegative : 0 ≤ smearRadius
  onsagerConstant : ℝ
  onsagerConstant_nonnegative : 0 ≤ onsagerConstant
  onsager : ∀ R N Γ, 0 < R → confined R N Γ →
    ((N : ℝ) - ρ * ballVolume R) ^ 2 / (2 * (R + smearRadius)) -
      onsagerConstant * N ≤ energy R Γ
  orbitalConstant : ℝ
  orbitalConstant_nonnegative : 0 ≤ orbitalConstant
  sample : ∀ R S N P Γ, 0 < R → R + 3 ≤ S → 0 < P → confined R N Γ →
    OrbitalSample energy confined R S N P Γ
      (RadialShells.energy (shellCharge ρ R S P) +
        ((N : ℝ) - ρ * ballVolume R) * potential (shellCharge ρ R S P) 0)
      ((P : ℝ) / trimmedVolume R S) orbitalConstant

/-- Canonical completion retaining the favorable outer-radius monopole term
from the appendix. The core charge can have either sign. Exact sampling
introduces no additional constant into the surface error. -/
theorem exists_neutral_completion_with_monopole {State : Type*}
    {energy : ℝ → State → ℝ} {confined : ℝ → ℕ → State → Prop} {ρ : ℝ}
    (laws : StandardLaws energy confined ρ) (hρ : 0 < ρ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ H D : ℝ, 0 ≤ H ∧ 0 ≤ D ∧ ∀ (R : ℝ) (N : ℕ) (Γ : State),
      1 ≤ R → confined R N Γ → energy R Γ ≤ C * R ^ 3 →
      ∃ (S : ℝ) (M : ℕ) (Ψ : State), R ≤ S ∧ S ≤ R + H ∧ ρ * ballVolume S = (M : ℝ) ∧
        confined S M Ψ ∧ energy S Ψ ≤ energy R Γ -
          ((N : ℝ) - ρ * ballVolume R) ^ 2 / (2 * S) + D * R ^ 2 := by
  let b := ρ * NeutralizationGeometry.ballFactor
  have hb : 0 ≤ b := mul_nonneg hρ.le NeutralizationGeometry.ballFactor_pos.le
  let K := 2 * (1 + laws.smearRadius) *
    (C + laws.onsagerConstant * b + laws.onsagerConstant) + 1
  have hK : 0 ≤ K := by
    dsimp [K]
    have := laws.smearRadius_nonnegative
    have := laws.onsagerConstant_nonnegative
    positivity
  obtain ⟨H, L, hH, hL, hgeometry⟩ :=
    NeutralizationGeometry.exists_prepared_annulus hρ hK
  let D := H * ((2 * L) ^ 2 / 2 + K * (2 * L)) +
    laws.orbitalConstant * (1 + L / NeutralizationGeometry.ballFactor) * L
  have hD : 0 ≤ D := by
    dsimp [D]
    have := laws.orbitalConstant_nonnegative
    have := NeutralizationGeometry.ballFactor_pos
    positivity
  refine ⟨H, D, hH.le, hD, ?_⟩
  intro R N Γ hR hΓ hupper
  have hR0 : 0 < R := by linarith
  have hcharge : |(N : ℝ) - ρ * ballVolume R| ≤ K * R ^ 2 := by
    have hbg : b * R ^ 3 = ρ * ballVolume R := by
      dsimp [b, NeutralizationGeometry.ballFactor, ballVolume]
      ring
    have h := charge_bound R N (energy R Γ) laws.smearRadius laws.onsagerConstant b C
      hR laws.smearRadius_nonnegative laws.onsagerConstant_nonnegative hb hC hupper
      (by simpa only [hbg] using laws.onsager R N Γ hR0 hΓ)
    simpa only [hbg] using h
  obtain ⟨g⟩ := hgeometry R N hR hcharge
  obtain ⟨hm, hi, hs, hmass, hL1⟩ := shellCharge_properties hρ hR g
  have hcorrection := shell_correction_bound_at_outer_radius
    (shellCharge ρ R g.radius g.particles) R g.radius
    (-((N : ℝ) - ρ * ballVolume R)) K (2 * L) hR0
    (by linarith [g.radius_lower]) hK (by positivity) hi
    (shellCharge_support ρ R g.radius g.particles) hmass
    (by simpa only [abs_neg] using hcharge) hL1
    (radial_self_integrable _ R H hR0 hm hi hs)
  simp only [neg_mul, sub_neg_eq_add, neg_sq] at hcorrection
  obtain ⟨Ψ, hΨ, heΨ⟩ := select_orbitals
    (laws.sample R g.radius N g.particles Γ hR0 g.radius_lower g.particles_pos hΓ)
  refine ⟨g.radius, g.total, Ψ, by linarith [g.radius_lower], g.radius_upper,
    g.neutral, ?_, ?_⟩
  · have hc : N + g.particles = g.total := (Nat.add_comm _ _).trans g.count
    exact hc ▸ hΨ
  · have htrim : 0 < trimmedVolume R g.radius :=
      lt_of_lt_of_le (by have := NeutralizationGeometry.ballFactor_pos; positivity) g.trimmed_lower
    have hd : 0 ≤ (g.particles : ℝ) / trimmedVolume R g.radius := by positivity
    have hcost : laws.orbitalConstant * (1 + (g.particles : ℝ) / trimmedVolume R g.radius) *
        g.particles ≤ laws.orbitalConstant * (1 + L / NeutralizationGeometry.ballFactor) *
          L * R ^ 2 := by
      have hcoef : laws.orbitalConstant *
          (1 + (g.particles : ℝ) / trimmedVolume R g.radius) ≤
          laws.orbitalConstant * (1 + L / NeutralizationGeometry.ballFactor) := by
        apply mul_le_mul_of_nonneg_left _ laws.orbitalConstant_nonnegative
        change 1 + (g.particles : ℝ) /
          (ballVolume (g.radius - 1) - ballVolume (R + 1)) ≤ _
        linarith only [g.sampling_bound]
      calc
        _ ≤ (laws.orbitalConstant * (1 + L / NeutralizationGeometry.ballFactor)) *
            (L * R ^ 2) := mul_le_mul hcoef g.particles_le (Nat.cast_nonneg _)
              (by have := laws.orbitalConstant_nonnegative
                  have := NeutralizationGeometry.ballFactor_pos
                  positivity)
        _ = _ := by ring
    have hc' : RadialShells.energy (shellCharge ρ R g.radius g.particles) +
        ((N : ℝ) - ρ * ballVolume R) * potential (shellCharge ρ R g.radius g.particles) 0 ≤
        -((N : ℝ) - ρ * ballVolume R) ^ 2 / (2 * g.radius) +
          H * ((2 * L) ^ 2 / 2 + K * (2 * L)) * R ^ 2 := by
      have hwidth := mul_le_mul_of_nonneg_right
        (show g.radius - R ≤ H by linarith [g.radius_upper])
        (show 0 ≤ ((2 * L) ^ 2 / 2 + K * (2 * L)) * R ^ 2 by positivity)
      nlinarith only [hcorrection, hwidth]
    have hself : 0 ≤ (laws.sample R g.radius N g.particles Γ hR0
        g.radius_lower g.particles_pos hΓ).omittedSelf / (g.particles : ℝ) :=
      div_nonneg (laws.sample R g.radius N g.particles Γ hR0
        g.radius_lower g.particles_pos hΓ).omittedSelf_nonnegative (Nat.cast_nonneg _)
    have hsum := add_le_add (add_le_add_left hc' (energy R Γ)) hcost
    apply (heΨ.trans (sub_le_self _ hself)).trans
    convert hsum using 1 <;> ring

/-- Uniform finite-volume canonical completion, obtained by constructing a
shell and selecting a sampled orbital state. Dropping the nonpositive
monopole term gives the form used by the thermodynamic lower comparison. -/
theorem exists_neutral_completion {State : Type*}
    {energy : ℝ → State → ℝ} {confined : ℝ → ℕ → State → Prop} {ρ : ℝ}
    (laws : StandardLaws energy confined ρ) (hρ : 0 < ρ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ H D : ℝ, 0 ≤ H ∧ 0 ≤ D ∧ ∀ (R : ℝ) (N : ℕ) (Γ : State),
      1 ≤ R → confined R N Γ → energy R Γ ≤ C * R ^ 3 →
      ∃ (S : ℝ) (M : ℕ) (Ψ : State), R ≤ S ∧ S ≤ R + H ∧ ρ * ballVolume S = (M : ℝ) ∧
        confined S M Ψ ∧ energy S Ψ ≤ energy R Γ + D * R ^ 2 := by
  obtain ⟨H, D, hH, hD, complete⟩ :=
    exists_neutral_completion_with_monopole laws hρ C hC
  refine ⟨H, D, hH, hD, ?_⟩
  intro R N Γ hR hΓ hupper
  obtain ⟨S, M, Ψ, hRS, hS, hneutral, hΨ, he⟩ := complete R N Γ hR hΓ hupper
  refine ⟨S, M, Ψ, hRS, hS, hneutral, hΨ, ?_⟩
  have hnonnegative : 0 ≤ ((N : ℝ) - ρ * ballVolume R) ^ 2 / (2 * S) :=
    div_nonneg (sq_nonneg _) (by linarith)
  linarith only [he, hnonnegative]

end Jellium.Neutralization
