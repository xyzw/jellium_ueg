import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Integral checks for the compensated collar.

The correction profile is defined here, and its weighted integral is proved to
vanish. The radial integration formula and Newton's field-energy formula are
not formalized here. The final theorem states the latter as an explicit
equality, so its analytic interface remains visible.
-/

open MeasureTheory Set

namespace Jellium.Collar

noncomputable def missingMass (s weight : ℝ → ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 2, (1 - s t ^ 2) * weight t

noncomputable def profileMass (ψ weight : ℝ → ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 2, ψ t * weight t

/-- The added profile is supported in the outer half of the collar, so this
denominator is the one displayed in the manuscript. -/
theorem profile_mass_outer_interval
    (ψ weight : ℝ → ℝ) (hsupport : Function.support ψ ⊆ Icc 1 2) :
    profileMass ψ weight = ∫ t in Icc (1 : ℝ) 2, ψ t * weight t := by
  unfold profileMass
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
  · intro t ht
    exact ⟨le_trans (by norm_num : (0 : ℝ) ≤ 1) ht.1, ht.2⟩
  · intro t ht
    have hzero : ψ t = 0 := by
      by_contra hnonzero
      exact ht.2 (hsupport hnonzero)
    simp [hzero]

noncomputable def coefficient (s ψ weight : ℝ → ℝ) : ℝ :=
  missingMass s weight / profileMass ψ weight

noncomputable def correctedProfile (s ψ weight : ℝ → ℝ) (t : ℝ) : ℝ :=
  s t ^ 2 + coefficient s ψ weight * ψ t

/-- Exact neutrality for the defined corrected profile, including the radial
Jacobian through the arbitrary weight. For the manuscript, use
`weight t = (r + a * t) ^ 2`. -/
theorem corrected_profile_neutral
    (s ψ weight : ℝ → ℝ)
    (hmissing : IntegrableOn (fun t => (1 - s t ^ 2) * weight t) (Icc 0 2))
    (hprofile : IntegrableOn (fun t => ψ t * weight t) (Icc 0 2))
    (hnonzero : profileMass ψ weight ≠ 0) :
    (∫ t in Icc (0 : ℝ) 2,
      (correctedProfile s ψ weight t - 1) * weight t) = 0 := by
  have hfunction :
      (fun t => (correctedProfile s ψ weight t - 1) * weight t) =
      (fun t => -((1 - s t ^ 2) * weight t) +
        coefficient s ψ weight * (ψ t * weight t)) := by
    funext t
    unfold correctedProfile
    ring
  have hneg : IntegrableOn (fun t => -((1 - s t ^ 2) * weight t)) (Icc 0 2) :=
    hmissing.neg
  have hcomp : IntegrableOn
      (fun t => coefficient s ψ weight * (ψ t * weight t)) (Icc 0 2) :=
    hprofile.const_mul (coefficient s ψ weight)
  rw [hfunction, integral_add hneg hcomp, integral_neg, integral_const_mul]
  change -missingMass s weight + coefficient s ψ weight * profileMass ψ weight = 0
  unfold coefficient
  field_simp
  ring

/-- The radial charge integral after the change of variable `radius = r + a*t`.
The overall density and Jacobian factors preserve exact neutrality. The
manuscript uses `sphereFactor = 4 * π`. -/
theorem radial_charge_neutral
    (s ψ : ℝ → ℝ) (sphereFactor r a ρ : ℝ)
    (hmissing : IntegrableOn
      (fun t => (1 - s t ^ 2) * (r + a * t) ^ 2) (Icc 0 2))
    (hprofile : IntegrableOn
      (fun t => ψ t * (r + a * t) ^ 2) (Icc 0 2))
    (hnonzero : profileMass ψ (fun t => (r + a * t) ^ 2) ≠ 0) :
    sphereFactor * ρ * a *
      (∫ t in Icc (0 : ℝ) 2,
        (correctedProfile s ψ (fun t => (r + a * t) ^ 2) t - 1) *
          (r + a * t) ^ 2) = 0 := by
  rw [corrected_profile_neutral s ψ (fun t => (r + a * t) ^ 2)
    hmissing hprofile hnonzero]
  ring

/-- The elementary integral bound behind the field-energy estimate. -/
theorem annular_integral_bound
    (Q : ℝ → ℝ) {r a M : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hint : IntegrableOn (fun t => Q t ^ 2 / t ^ 2) (Icc r (r + 2 * a)))
    (hQ : ∀ t ∈ Icc r (r + 2 * a), |Q t| ≤ M) :
    (1 / 2 : ℝ) * (∫ t in Icc r (r + 2 * a), Q t ^ 2 / t ^ 2) ≤
      a * M ^ 2 / r ^ 2 := by
  have hpoint : ∀ t ∈ Icc r (r + 2 * a), Q t ^ 2 / t ^ 2 ≤ M ^ 2 / r ^ 2 := by
    intro t ht
    have hQsq : Q t ^ 2 ≤ M ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Q t)) hM).2 (hQ t ht)
    have ht_nonneg : 0 ≤ t := le_trans (le_of_lt hr) ht.1
    have hrsq : r ^ 2 ≤ t ^ 2 := (sq_le_sq₀ (le_of_lt hr) ht_nonneg).2 ht.1
    exact div_le_div₀ (sq_nonneg M) hQsq (sq_pos_of_pos hr) hrsq
  have hconst : IntegrableOn (fun _ : ℝ => M ^ 2 / r ^ 2) (Icc r (r + 2 * a)) :=
    integrableOn_const (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hbound := setIntegral_mono_on hint hconst measurableSet_Icc hpoint
  have hvolume : volume.real (Icc r (r + 2 * a)) = 2 * a := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [setIntegral_const, smul_eq_mul, hvolume] at hbound
  calc
    (1 / 2 : ℝ) * (∫ t in Icc r (r + 2 * a), Q t ^ 2 / t ^ 2) ≤
        (1 / 2 : ℝ) * (2 * a * (M ^ 2 / r ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = a * M ^ 2 / r ^ 2 := by ring

noncomputable def radialFieldEnergy (Q : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t : ℝ, Q t ^ 2 / t ^ 2

/-- Support in the annulus reduces the full radial field integral to the
preceding estimate. Integrability is stated explicitly. -/
theorem radial_field_energy_bound
    (Q : ℝ → ℝ) {r a M : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hint : IntegrableOn (fun t => Q t ^ 2 / t ^ 2) (Icc r (r + 2 * a)))
    (hsupport : ∀ t, t ∉ Icc r (r + 2 * a) → Q t = 0)
    (hQ : ∀ t ∈ Icc r (r + 2 * a), |Q t| ≤ M) :
    radialFieldEnergy Q ≤ a * M ^ 2 / r ^ 2 := by
  have hrestrict : (∫ t in Icc r (r + 2 * a), Q t ^ 2 / t ^ 2) =
      ∫ t : ℝ, Q t ^ 2 / t ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    simp [hsupport t ht]
  unfold radialFieldEnergy
  rw [← hrestrict]
  exact annular_integral_bound Q hr ha hM hint hQ

/-- Newton's field-energy equality is the explicit analytic input `hfield`.
The resulting bound has exactly the surface scaling of the manuscript. -/
theorem collar_coulomb_bound
    (Q : ℝ → ℝ) {D C ρ r a : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hint : IntegrableOn (fun t => Q t ^ 2 / t ^ 2) (Icc r (r + 2 * a)))
    (hsupport : ∀ t, t ∉ Icc r (r + 2 * a) → Q t = 0)
    (hQ : ∀ t ∈ Icc r (r + 2 * a), |Q t| ≤ C * ρ * r ^ 2 * a)
    (hfield : D = radialFieldEnergy Q) :
    D ≤ C ^ 2 * ρ ^ 2 * r ^ 2 * a ^ 3 := by
  rw [hfield]
  have hbound := radial_field_energy_bound Q hr ha
    (by positivity : 0 ≤ C * ρ * r ^ 2 * a) hint hsupport hQ
  have heq : a * (C * ρ * r ^ 2 * a) ^ 2 / r ^ 2 =
      C ^ 2 * ρ ^ 2 * r ^ 2 * a ^ 3 := by
    field_simp [ne_of_gt hr]
  exact le_trans hbound (le_of_eq heq)

end Jellium.Collar
