import Jellium.SmoothCollar
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Module.Submodule.Basic

/-!
The actual Euclidean radial collar. Standard polar integration, radial
Dirichlet integration, and Newton field identities are isolated as general
laws for arbitrary radial profiles. Support, positivity, compensation,
regularity and surface-order estimates for the constructed collar are proved.
-/

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace Jellium.RadialCollar

abbrev Space := EuclideanSpace ℝ (Fin 3)

noncomputable def coeff (r a : ℝ) : ℝ :=
  Collar.coefficient SmoothCollar.cutoff SmoothCollar.bump (SmoothCollar.weight r a)

noncomputable def amplitude : ℝ := 1 + 9 / (4 * SmoothCollar.bumpMass)

theorem amplitude_ge_one : 1 ≤ amplitude := by
  have hb := SmoothCollar.bumpMass_pos
  have hp : 0 ≤ 9 / (4 * SmoothCollar.bumpMass) := by positivity
  unfold amplitude
  linarith

noncomputable def root (z : Space) (r a : ℝ) (x : Space) : ℝ :=
  SmoothCollar.rootProfile (coeff r a) ((dist x z - r) / a)

theorem root_nonneg (z : Space) (r a : ℝ) (x : Space) : 0 ≤ root z r a x :=
  SmoothCollar.rootProfile_nonneg _ _

theorem root_zero {z x : Space} {r a : ℝ} (ha : 0 < a)
    (hx : dist x z ≤ r + a / 4) : root z r a x = 0 := by
  apply SmoothCollar.rootProfile_zero
  apply (div_le_iff₀ ha).2
  linarith

theorem root_one {z x : Space} {r a : ℝ} (ha : 0 < a)
    (hx : r + 7 * a / 4 ≤ dist x z) : root z r a x = 1 := by
  apply SmoothCollar.rootProfile_one
  apply (le_div_iff₀ ha).2
  linarith

theorem root_sq_bound {z : Space} {r a : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) (x : Space) :
    root z r a x ^ 2 ≤ amplitude := by
  exact SmoothCollar.rootProfile_sq_bound
    (SmoothCollar.coefficient_nonneg hr ha har) (SmoothCollar.coefficient_bounds hr ha har).2

theorem root_smooth (z : Space) {r a : ℝ}
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) : ContDiff ℝ ∞ (root z r a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = z
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds z hr] with y hy
    apply root_zero ha
    have hy' : dist y z < r := hy
    linarith
  · have hdist : ContDiffAt ℝ ∞ (fun y : Space => dist y z) x :=
      contDiffAt_id.dist ℝ contDiffAt_const hx
    exact (SmoothCollar.rootProfile_smooth
      (SmoothCollar.coefficient_nonneg hr ha.le har)).contDiffAt.comp x
        ((hdist.sub contDiffAt_const).div_const a)

noncomputable def correction (z : Space) (r a ρ : ℝ) (x : Space) : ℝ :=
  Real.sqrt ρ * (root z r a x - 1)

theorem correction_smooth (z : Space) {r a : ℝ} (ρ : ℝ)
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) :
    ContDiff ℝ ∞ (correction z r a ρ) := by
  exact contDiff_const.mul ((root_smooth z hr ha har).sub contDiff_const)

theorem correction_compact (z : Space) {r a : ℝ} (ρ : ℝ) (ha : 0 < a) :
    HasCompactSupport (correction z r a ρ) := by
  apply HasCompactSupport.intro (isCompact_closedBall z (r + 2 * a))
  intro x hx
  have hdist : r + 2 * a < dist x z := lt_of_not_ge hx
  unfold correction
  rw [root_one ha (by linarith)]
  ring

theorem correction_support_inner (z : Space) {r a : ℝ} (ρ : ℝ) (ha : 0 < a) :
    Function.support (correction z r a ρ) ⊆ Metric.closedBall z (r + 7 * a / 4) := by
  intro x hx
  by_contra hout
  have hdist : r + 7 * a / 4 < dist x z := lt_of_not_ge hout
  apply hx
  unfold correction
  rw [root_one ha hdist.le]
  ring

theorem correction_tsupport_inner (z : Space) {r a : ℝ} (ρ : ℝ) (ha : 0 < a) :
    tsupport (correction z r a ρ) ⊆ Metric.closedBall z (r + 7 * a / 4) := by
  exact closure_minimal (correction_support_inner z ρ ha) Metric.isClosed_closedBall

/-- The standard inclusion of smooth compactly supported functions in H¹
applied to the constructed correction. This is the exact Gluing interface. -/
theorem correction_mem
    (H1 : Submodule ℝ (Space → ℝ))
    (hsmooth_mem : ∀ f : Space → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → f ∈ H1)
    (z : Space) {r a : ℝ} (ρ : ℝ)
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) :
    correction z r a ρ ∈ H1 :=
  hsmooth_mem _ (correction_smooth z ρ hr ha har) (correction_compact z ρ ha)

noncomputable def shellLift (z : Space) (r a : ℝ) (F : ℝ → ℝ) (x : Space) : ℝ := by
  classical
  exact if r < dist x z ∧ dist x z < r + 2 * a then F ((dist x z - r) / a) else 0

noncomputable def chargeProfile (r a ρ t : ℝ) : ℝ :=
  ρ * (SmoothCollar.rootProfile (coeff r a) t ^ 2 - 1)

noncomputable def charge (z : Space) (r a ρ : ℝ) : Space → ℝ :=
  shellLift z r a (chargeProfile r a ρ)

theorem charge_core {z x : Space} {r a ρ : ℝ} (hx : dist x z ≤ r) :
    charge z r a ρ x = 0 := by
  simp [charge, shellLift, not_lt_of_ge hx]

theorem charge_outside {z x : Space} {r a ρ : ℝ} (hx : r + 2 * a ≤ dist x z) :
    charge z r a ρ x = 0 := by
  simp [charge, shellLift, not_lt_of_ge hx]

theorem charge_support (z : Space) (r a ρ : ℝ) :
    Function.support (charge z r a ρ) ⊆
      Metric.closedBall z (r + 2 * a) \ Metric.closedBall z r := by
  intro x hx
  constructor
  · by_contra hout
    exact hx (charge_outside (le_of_lt (lt_of_not_ge hout)))
  · intro hcore
    exact hx (charge_core hcore)

theorem root_one_outside {z x : Space} {r a : ℝ} (ha : 0 < a)
    (hx : x ∉ Metric.closedBall z (r + 2 * a)) : root z r a x = 1 := by
  apply root_one ha
  have hdist : r + 2 * a < dist x z := lt_of_not_ge hx
  linarith

theorem charge_compact (z : Space) (r a ρ : ℝ) : HasCompactSupport (charge z r a ρ) := by
  apply HasCompactSupport.intro (isCompact_closedBall z (r + 2 * a))
  intro x hx
  exact charge_outside (le_of_lt (lt_of_not_ge hx))

theorem density_on_shell {z x : Space} {r a ρ : ℝ}
    (ha : 0 < a) (hx : r < dist x z) :
    ρ + charge z r a ρ x = ρ * root z r a x ^ 2 := by
  by_cases hout : dist x z < r + 2 * a
  · simp only [charge, shellLift, hx, hout, and_self, ite_true, chargeProfile, root]
    ring
  · rw [charge_outside (le_of_not_gt hout), root_one ha (by linarith)]
    ring

noncomputable def coreBackground (z : Space) (r ρ : ℝ) (x : Space) : ℝ := by
  classical
  exact if dist x z ≤ r then ρ else 0

theorem density_decomposition (z : Space) {r a : ℝ} (ρ : ℝ) (ha : 0 < a) (x : Space) :
    ρ * root z r a x ^ 2 = ρ - coreBackground z r ρ x + charge z r a ρ x := by
  classical
  by_cases hx : dist x z ≤ r
  · rw [root_zero ha (by linarith), charge_core hx]
    simp [coreBackground, hx]
  · have hshell := (density_on_shell (ρ := ρ) ha (lt_of_not_ge hx)).symm
    simpa [coreBackground, hx] using hshell

theorem profile_bound {r a ρ : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) (hρ : 0 ≤ ρ) (t : ℝ) :
    |chargeProfile r a ρ t| ≤ amplitude * ρ := by
  have hupper := SmoothCollar.rootProfile_sq_bound
    (SmoothCollar.coefficient_nonneg hr ha har)
    (SmoothCollar.coefficient_bounds hr ha har).2 (t := t)
  have hH := amplitude_ge_one
  have hsquare := sq_nonneg (SmoothCollar.rootProfile (coeff r a) t)
  apply abs_le.2
  unfold chargeProfile
  change SmoothCollar.rootProfile (coeff r a) t ^ 2 ≤ amplitude at hupper
  constructor <;> nlinarith [mul_nonneg hρ (sub_nonneg.2 hH),
    mul_le_mul_of_nonneg_left hupper hρ, mul_nonneg hρ hsquare]

theorem charge_bound (z : Space) {r a ρ : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) (hρ : 0 ≤ ρ) (x : Space) :
    |charge z r a ρ x| ≤ amplitude * ρ := by
  classical
  unfold charge shellLift
  split_ifs
  · exact profile_bound hr ha har hρ _
  · have hH := amplitude_ge_one
    simp only [abs_zero]
    positivity

def RadialAbout (z : Space) (f : Space → ℝ) : Prop :=
  ∃ F : ℝ → ℝ, ∀ x, f x = F (dist x z)

theorem charge_radial (z : Space) (r a ρ : ℝ) : RadialAbout z (charge z r a ρ) := by
  classical
  exact ⟨fun t => if r < t ∧ t < r + 2 * a then chargeProfile r a ρ ((t - r) / a) else 0,
    fun _ => rfl⟩

/-- Standard polar integration, including the affine radial substitution,
stated for arbitrary continuous profiles. -/
def PolarLaw (μ : Measure Space) (sf : ℝ) : Prop :=
  ∀ (z : Space) (r a : ℝ) (F : ℝ → ℝ), 0 < r → 0 < a →
    ContinuousOn F (Icc 0 2) →
    Integrable (shellLift z r a F) μ ∧
      (∫ x, shellLift z r a F x ∂μ) =
        sf * a * ∫ t in Icc (0 : ℝ) 2, F t * SmoothCollar.weight r a t

theorem profile_continuous {r a : ℝ} (ρ : ℝ)
    (hr : 0 < r) (ha : 0 ≤ a) (har : 2 * a ≤ r) :
    Continuous (chargeProfile r a ρ) := by
  exact continuous_const.mul
    (((SmoothCollar.rootProfile_smooth (SmoothCollar.coefficient_nonneg hr ha har)).continuous.pow 2).sub
      continuous_const)

theorem charge_integrable
    {μ : Measure Space} {sf : ℝ} (hpolar : PolarLaw μ sf)
    (z : Space) {r a : ℝ} (ρ : ℝ)
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) :
    Integrable (charge z r a ρ) μ :=
  (hpolar z r a (chargeProfile r a ρ) hr ha (profile_continuous ρ hr ha.le har).continuousOn).1

theorem charge_neutral
    {μ : Measure Space} {sf : ℝ} (hpolar : PolarLaw μ sf)
    (z : Space) {r a : ℝ} (ρ : ℝ)
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) :
    (∫ x, charge z r a ρ x ∂μ) = 0 := by
  unfold charge
  rw [(hpolar z r a (chargeProfile r a ρ) hr ha
    (profile_continuous ρ hr ha.le har).continuousOn).2]
  have hfunction : (fun t => chargeProfile r a ρ t * SmoothCollar.weight r a t) =
      fun t => ρ * ((Collar.correctedProfile SmoothCollar.cutoff SmoothCollar.bump
        (SmoothCollar.weight r a) t - 1) * SmoothCollar.weight r a t) := by
    funext t
    unfold chargeProfile coeff
    rw [SmoothCollar.rootProfile_sq (SmoothCollar.coefficient_nonneg hr ha.le har)]
    unfold Collar.correctedProfile
    ring
  rw [hfunction, integral_const_mul, SmoothCollar.correction_neutral hr ha.le har]
  ring

theorem charge_l1_bound
    {μ : Measure Space} {sf : ℝ} (hpolar : PolarLaw μ sf) (hsf : 0 ≤ sf)
    (z : Space) {r a ρ : ℝ}
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) (hρ : 0 ≤ ρ) :
    (∫ x, |charge z r a ρ x| ∂μ) ≤ (8 * sf * amplitude) * ρ * r ^ 2 * a := by
  have hc := profile_continuous ρ hr ha.le har
  have habs : (fun x => |charge z r a ρ x|) =
      shellLift z r a (fun t => |chargeProfile r a ρ t|) := by
    funext x
    unfold charge shellLift
    split_ifs <;> simp
  rw [habs, (hpolar z r a (fun t => |chargeProfile r a ρ t|) hr ha hc.abs.continuousOn).2]
  have hweight : Continuous (SmoothCollar.weight r a) :=
    (continuous_const.add (continuous_const.mul continuous_id)).pow 2
  have hint : IntegrableOn
      (fun t => |chargeProfile r a ρ t| * SmoothCollar.weight r a t) (Icc 0 2) :=
    (hc.abs.mul hweight).continuousOn.integrableOn_Icc
  have hconst : IntegrableOn (fun _ : ℝ => amplitude * ρ * (4 * r ^ 2)) (Icc 0 2) :=
    continuous_const.continuousOn.integrableOn_Icc
  have hH : 0 ≤ amplitude := le_trans zero_le_one amplitude_ge_one
  have hpoint := setIntegral_mono_on hint hconst measurableSet_Icc (fun t ht =>
    mul_le_mul (profile_bound hr ha.le har hρ t)
      (SmoothCollar.weight_upper hr.le ha.le har ht)
      (SmoothCollar.weight_nonneg r a t) (mul_nonneg hH hρ))
  have hbound : (∫ t in Icc (0 : ℝ) 2,
      |chargeProfile r a ρ t| * SmoothCollar.weight r a t) ≤
      2 * (amplitude * ρ * (4 * r ^ 2)) := by
    simpa [setIntegral_const, measureReal_def, Real.volume_Icc] using hpoint
  calc
    sf * a * (∫ t in Icc (0 : ℝ) 2,
        |chargeProfile r a ρ t| * SmoothCollar.weight r a t) ≤
        sf * a * (2 * (amplitude * ρ * (4 * r ^ 2))) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hsf ha.le)
    _ = (8 * sf * amplitude) * ρ * r ^ 2 * a := by ring

noncomputable def enclosed (μ : Measure Space) (z : Space) (g : Space → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Metric.closedBall z t, g x ∂μ

theorem enclosed_abs_le (μ : Measure Space) (z : Space) (g : Space → ℝ)
    (hg : Integrable g μ) (t : ℝ) : |enclosed μ z g t| ≤ ∫ x, |g x| ∂μ := by
  have habs : Integrable (fun x => |g x|) μ := by simpa only [Real.norm_eq_abs] using hg.norm
  calc
    |enclosed μ z g t| ≤ ∫ x in Metric.closedBall z t, |g x| ∂μ := by
      simpa only [enclosed, Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (f := g) (μ := μ.restrict (Metric.closedBall z t)))
    _ ≤ ∫ x, |g x| ∂μ := setIntegral_le_integral habs (ae_of_all _ (fun x => abs_nonneg (g x)))

theorem enclosed_support
    {μ : Measure Space} {sf : ℝ} (hpolar : PolarLaw μ sf)
    (z : Space) {r a : ℝ} (ρ : ℝ)
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) :
    ∀ t, t ∉ Icc r (r + 2 * a) → enclosed μ z (charge z r a ρ) t = 0 := by
  intro t ht
  by_cases hlow : t < r
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply charge_core
    have hdist : dist x z ≤ t := hx
    linarith
  · have hhigh : r + 2 * a < t := by
      by_contra hn
      exact ht ⟨le_of_not_gt hlow, le_of_not_gt hn⟩
    have heq : enclosed μ z (charge z r a ρ) t = ∫ x, charge z r a ρ x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hdist : t < dist x z := lt_of_not_ge hx
      exact charge_outside (by linarith)
    rw [heq, charge_neutral hpolar z ρ hr ha har]

/-- Newton's theorem and the field-energy identity, for arbitrary bounded
integrable compactly supported radial neutral charges. The local integrability
clause is the usual regularity of the enclosed-charge field away from zero. -/
def NewtonLaw (μ : Measure Space) (energy : (Space → ℝ) → ℝ) : Prop :=
  ∀ (z : Space) (g : Space → ℝ), Integrable g μ → HasCompactSupport g →
    RadialAbout z g → (∃ B : ℝ, ∀ x, |g x| ≤ B) → (∫ x, g x ∂μ) = 0 →
    energy g = Collar.radialFieldEnergy (enclosed μ z g) ∧
      ∀ r a : ℝ, 0 < r → 0 ≤ a →
        IntegrableOn (fun t => enclosed μ z g t ^ 2 / t ^ 2) (Icc r (r + 2 * a))

/-- The exterior part of the standard Newton theorem for arbitrary radial
integrable neutral charges supported in a ball. -/
def ExteriorNewtonLaw (μ : Measure Space)
    (potential : (Space → ℝ) → Space → ℝ) : Prop :=
  ∀ (z : Space) (R : ℝ) (g : Space → ℝ), 0 < R → Integrable g μ →
    RadialAbout z g → (∀ x, x ∉ Metric.closedBall z R → g x = 0) →
    (∫ x, g x ∂μ) = 0 → ∀ x, x ∉ Metric.closedBall z R → potential g x = 0

theorem charge_zero_potential
    {μ : Measure Space} {sf : ℝ} {potential : (Space → ℝ) → Space → ℝ}
    (hpolar : PolarLaw μ sf) (hnewton : ExteriorNewtonLaw μ potential)
    (z : Space) {r a : ℝ} (ρ : ℝ)
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) :
    ∀ x, x ∉ Metric.closedBall z (r + 2 * a) → potential (charge z r a ρ) x = 0 := by
  apply hnewton z (r + 2 * a) (charge z r a ρ) (by positivity)
    (charge_integrable hpolar z ρ hr ha har) (charge_radial z r a ρ)
    _ (charge_neutral hpolar z ρ hr ha har)
  intro x hx
  exact charge_outside (le_of_lt (lt_of_not_ge hx))

theorem coulomb_cost
    {μ : Measure Space} {sf : ℝ} {energy : (Space → ℝ) → ℝ}
    (hpolar : PolarLaw μ sf) (hsf : 0 ≤ sf) (hnewton : NewtonLaw μ energy)
    (z : Space) {r a ρ : ℝ}
    (hr : 0 < r) (ha : 0 < a) (har : 2 * a ≤ r) (hρ : 0 ≤ ρ) :
    energy (charge z r a ρ) ≤ (8 * sf * amplitude) ^ 2 * ρ ^ 2 * r ^ 2 * a ^ 3 := by
  have hg := charge_integrable hpolar z ρ hr ha har
  obtain ⟨hfield, hint⟩ := hnewton z (charge z r a ρ) hg (charge_compact z r a ρ)
    (charge_radial z r a ρ) ⟨amplitude * ρ, charge_bound z hr ha.le har hρ⟩
    (charge_neutral hpolar z ρ hr ha har)
  have hH : 0 ≤ amplitude := le_trans zero_le_one amplitude_ge_one
  apply Collar.collar_coulomb_bound (enclosed μ z (charge z r a ρ)) hr ha.le
    (by positivity : 0 ≤ 8 * sf * amplitude) hρ (hint r a hr ha.le)
    (enclosed_support hpolar z ρ hr ha har) _ hfield
  intro t _ht
  exact le_trans (enclosed_abs_le μ z (charge z r a ρ) hg t)
    (charge_l1_bound hpolar hsf z hr ha har hρ)

noncomputable def radialCorrection (z : Space) (r a ρ : ℝ) (u : ℝ → ℝ) (x : Space) : ℝ :=
  Real.sqrt ρ * (u ((dist x z - r) / a) - 1)

/-- Standard radial chain rule and polar-coordinate formula for the Dirichlet
integral, for arbitrary smooth profiles constant at the two ends. -/
def DirichletLaw (sf : ℝ) (energy : (Space → ℝ) → ℝ) : Prop :=
  ∀ (z : Space) (r a ρ : ℝ) (u : ℝ → ℝ), 0 < r → 0 < a → 0 ≤ ρ →
    ContDiff ℝ ∞ u → (∀ t, t ≤ 0 → u t = 0) → (∀ t, 2 ≤ t → u t = 1) →
    energy (radialCorrection z r a ρ u) =
      sf * ρ / a * ∫ t in Icc (0 : ℝ) 2, deriv u t ^ 2 * SmoothCollar.weight r a t

theorem exists_uniform_gradient_cost
    {sf : ℝ} {energy : (Space → ℝ) → ℝ} (hsf : 0 ≤ sf)
    (hdirichlet : DirichletLaw sf energy) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : Space) (r a ρ : ℝ),
      0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
        energy (correction z r a ρ) ≤ K * ρ * r ^ 2 / a := by
  obtain ⟨K, hK, hprofileK⟩ := SmoothCollar.exists_uniform_gradient_integral
  refine ⟨4 * sf * K, by positivity, ?_⟩
  intro z r a ρ hr ha har hρ
  let u : ℝ → ℝ := SmoothCollar.rootProfile (coeff r a)
  have hc := SmoothCollar.coefficient_nonneg hr ha.le har
  have hsmooth : ContDiff ℝ ∞ u := SmoothCollar.rootProfile_smooth hc
  have hcost := hdirichlet z r a ρ u hr ha hρ hsmooth
    (fun t ht => SmoothCollar.rootProfile_zero (by linarith))
    (fun t ht => SmoothCollar.rootProfile_one (by linarith))
  change energy (correction z r a ρ) = _ at hcost
  rw [hcost]
  have hderiv := (hsmooth.continuous_deriv (by simp)).pow 2
  have hweight : Continuous (SmoothCollar.weight r a) :=
    (continuous_const.add (continuous_const.mul continuous_id)).pow 2
  have hint : IntegrableOn
      (fun t : ℝ => deriv u t ^ 2 * SmoothCollar.weight r a t) (Icc 0 2) :=
    (hderiv.mul hweight).continuousOn.integrableOn_Icc
  have hupper : IntegrableOn (fun t : ℝ => 4 * r ^ 2 * deriv u t ^ 2) (Icc 0 2) :=
    (hderiv.const_mul (4 * r ^ 2)).continuousOn.integrableOn_Icc
  have hmono := setIntegral_mono_on hint hupper measurableSet_Icc (fun t ht => by
    have h := mul_le_mul_of_nonneg_left (SmoothCollar.weight_upper hr.le ha.le har ht)
      (sq_nonneg (deriv u t))
    nlinarith)
  rw [integral_const_mul] at hmono
  have hscalar := hprofileK (coeff r a) hc (SmoothCollar.coefficient_bounds hr ha.le har).2
  have hweighted : (∫ t in Icc (0 : ℝ) 2, deriv u t ^ 2 * SmoothCollar.weight r a t) ≤
      4 * r ^ 2 * K := le_trans hmono (mul_le_mul_of_nonneg_left hscalar (by positivity))
  calc
    sf * ρ / a * (∫ t in Icc (0 : ℝ) 2, deriv u t ^ 2 * SmoothCollar.weight r a t) ≤
        sf * ρ / a * (4 * r ^ 2 * K) := mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = (4 * sf * K) * ρ * r ^ 2 / a := by ring

end Jellium.RadialCollar
