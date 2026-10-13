import Jellium.Packing
import Jellium.RadialCollar
import Jellium.FluidRegularity

/-!
Realization of finite neutral-ball trial states from the actual radial collars.
No `FluidGeometry` or fluid regularity is supplied by the caller. Charge-space
membership, Sobolev locality and the Fock operations are standard interfaces.
-/

open Set Finset MeasureTheory
open scoped ContDiff

namespace Jellium.UpperConstruction

abbrev Space := RadialCollar.Space

universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable (C : TrialState.ChargeModel Space V)

structure BallFamily (n : ℕ) (a : ℝ) where
  center : Fin n → Space
  radius : Fin n → ℝ
  radius_pos : ∀ i, 0 < radius i
  collar_room : ∀ i, 2 * a ≤ radius i
  disjoint : Pairwise fun i j =>
    Disjoint (Metric.closedBall (center i) (radius i + 2 * a))
      (Metric.closedBall (center j) (radius j + 2 * a))

def BallFamily.ofPacking {ρ κ a rmin ε : ℝ}
    (p : Packing.NeutralPacking ρ κ a rmin ε)
    (hrmin : 0 < rmin) (hroom : 2 * a ≤ rmin) : BallFamily p.count a where
  center := p.center
  radius := p.radius
  radius_pos := fun i => lt_of_lt_of_le hrmin (p.radius_min i)
  collar_room := fun i => le_trans hroom (p.radius_min i)
  disjoint := p.collars_disjoint

/-- Standard membership in the finite-charge space, for arbitrary bounded
integrable compactly supported functions. This premise is not collar-specific. -/
def Representations : Prop :=
  ∀ f : Space → ℝ, Integrable f C.measure → HasCompactSupport f →
    (∃ M : ℝ, ∀ x, |f x| ≤ M) → ∃ q : V, C.eval q = f

structure LocalRepresentatives {n : ℕ} {a : ℝ} (F : BallFamily n a) (ρ : ℝ) where
  core : Fin n → V
  collar : Fin n → V
  core_eval : ∀ i, C.eval (core i) = RadialCollar.coreBackground (F.center i) (F.radius i) ρ
  collar_eval : ∀ i, C.eval (collar i) = RadialCollar.charge (F.center i) (F.radius i) a ρ

theorem core_integrable [IsFiniteMeasureOnCompacts C.measure]
    (z : Space) (r ρ : ℝ) : Integrable (RadialCollar.coreBackground z r ρ) C.measure := by
  classical
  have hconst : IntegrableOn (fun _ : Space => ρ) (Metric.closedBall z r) C.measure :=
    integrableOn_const (isCompact_closedBall z r).measure_ne_top
  have heq : RadialCollar.coreBackground z r ρ =
      (Metric.closedBall z r).indicator (fun _ : Space => ρ) := by
    funext x
    simp [RadialCollar.coreBackground, Set.indicator, Metric.mem_closedBall]
  rw [heq]
  exact hconst.integrable_indicator Metric.isClosed_closedBall.measurableSet

theorem core_compact (z : Space) (r ρ : ℝ) :
    HasCompactSupport (RadialCollar.coreBackground z r ρ) := by
  classical
  apply HasCompactSupport.intro (isCompact_closedBall z r)
  intro x hx
  have hx' : ¬ dist x z ≤ r := hx
  simp [RadialCollar.coreBackground, hx']

theorem core_bound (z : Space) (r ρ : ℝ) (x : Space) :
    |RadialCollar.coreBackground z r ρ x| ≤ |ρ| := by
  classical
  unfold RadialCollar.coreBackground
  split_ifs <;> simp

theorem exists_local_representatives [IsFiniteMeasureOnCompacts C.measure]
    (hrepresent : Representations C)
    {sf a ρ : ℝ} {n : ℕ} (F : BallFamily n a)
    (hpolar : RadialCollar.PolarLaw C.measure sf) (ha : 0 < a) (hρ : 0 ≤ ρ) :
    Nonempty (LocalRepresentatives C F ρ) := by
  classical
  have hcore : ∀ i : Fin n, ∃ q : V,
      C.eval q = RadialCollar.coreBackground (F.center i) (F.radius i) ρ := by
    intro i
    exact hrepresent _ (core_integrable C _ _ _) (core_compact _ _ _)
      ⟨|ρ|, core_bound _ _ _⟩
  have hcollar : ∀ i : Fin n, ∃ q : V,
      C.eval q = RadialCollar.charge (F.center i) (F.radius i) a ρ := by
    intro i
    exact hrepresent _
      (RadialCollar.charge_integrable hpolar _ ρ (F.radius_pos i) ha (F.collar_room i))
      (RadialCollar.charge_compact _ _ _ _)
      ⟨RadialCollar.amplitude * ρ,
        RadialCollar.charge_bound _ (F.radius_pos i) ha.le (F.collar_room i) hρ⟩
  exact ⟨{
    core := fun i => Classical.choose (hcore i)
    collar := fun i => Classical.choose (hcollar i)
    core_eval := fun i => Classical.choose_spec (hcore i)
    collar_eval := fun i => Classical.choose_spec (hcollar i)
  }⟩

noncomputable def geometry
    {sf a ρ : ℝ} {n : ℕ} (F : BallFamily n a) (R : LocalRepresentatives C F ρ)
    (hpolar : RadialCollar.PolarLaw C.measure sf) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (β : V) (hβ0 : ∀ x, 0 ≤ C.eval β x) (hβle : ∀ x, C.eval β x ≤ ρ)
    (hplateau : ∀ i x, x ∈ Metric.closedBall (F.center i) (F.radius i + 2 * a) → C.eval β x = ρ) :
    TrialState.FluidGeometry C n ρ RadialCollar.amplitude := by
  classical
  exact {
    background := β
    coreBackground := R.core
    collar := R.collar
    core := fun i => Metric.closedBall (F.center i) (F.radius i)
    enlarged := fun i => Metric.closedBall (F.center i) (F.radius i + 2 * a)
    core_subset := fun i => Metric.closedBall_subset_closedBall (by linarith)
    disjoint := F.disjoint
    background_nonneg := hβ0
    background_le := hβle
    plateau := hplateau
    core_on := by
      intro i x hx
      rw [R.core_eval i]
      have hx' : dist x (F.center i) ≤ F.radius i := hx
      simp [RadialCollar.coreBackground, hx']
    core_off := by
      intro i x hx
      rw [R.core_eval i]
      have hx' : ¬ dist x (F.center i) ≤ F.radius i := hx
      simp [RadialCollar.coreBackground, hx']
    collar_outside := by
      intro i x hx
      rw [R.collar_eval i]
      exact RadialCollar.charge_outside (le_of_lt (lt_of_not_ge hx))
    collar_core := by
      intro i x hx
      rw [R.collar_eval i]
      exact RadialCollar.charge_core hx
    collar_profile := by
      intro i x _hx hcore
      rw [R.collar_eval i, RadialCollar.density_on_shell ha (lt_of_not_ge hcore)]
      constructor
      · positivity
      · have h := mul_le_mul_of_nonneg_left
          (RadialCollar.root_sq_bound (z := F.center i) (F.radius_pos i) ha.le (F.collar_room i) x) hρ
        nlinarith
    collar_neutral := by
      intro i
      rw [C.mass_integral, R.collar_eval i]
      exact RadialCollar.charge_neutral hpolar _ ρ (F.radius_pos i) ha (F.collar_room i)
  }

/-- Ordinary H¹ and Dirichlet-form laws. The bilinear form is defined on H¹,
not on arbitrary functions. Its two locality properties are general standard
facts and do not mention any packing or collar. -/
structure SobolevDirichlet {State : Type w} {h₂ cTF : ℝ}
    (S : TrialState.StateAPI C State h₂ cTF) (sf : ℝ) where
  H1 : Submodule ℝ (Space → ℝ)
  form : CoulombForm H1
  energy : (Space → ℝ) → ℝ
  energy_eq : ∀ f : H1, energy f = form.form f f
  smooth_mem : ∀ f : Space → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → f ∈ H1
  regular_iff : ∀ p : V, S.regular p ↔ (fun x => Real.sqrt (C.eval p x)) ∈ H1
  gradient_eq : ∀ p : V, S.regular p → S.gradient p = energy (fun x => Real.sqrt (C.eval p x))
  disjoint_locality : ∀ f g : H1, Disjoint (tsupport (f : Space → ℝ)) (tsupport (g : Space → ℝ)) →
    form.form f g = 0
  constant_locality : ∀ (f g : H1) (U : Set Space) (b : ℝ), IsOpen U →
    tsupport (g : Space → ℝ) ⊆ U → (∀ x ∈ U, (f : Space → ℝ) x = b) → form.form f g = 0
  radial_formula : RadialCollar.DirichletLaw sf energy

variable {C}
variable {State : Type w} {h₂ cTF sf a ρ : ℝ} {n : ℕ}
variable (S : TrialState.StateAPI C State h₂ cTF) (D : SobolevDirichlet C S sf)
variable (F : BallFamily n a) (R : LocalRepresentatives C F ρ)
variable (hpolar : RadialCollar.PolarLaw C.measure sf) (ha : 0 < a) (hρ : 0 ≤ ρ)
variable (β : V) (hβ0 : ∀ x, 0 ≤ C.eval β x) (hβle : ∀ x, C.eval β x ≤ ρ)
variable (hplateau : ∀ i x, x ∈ Metric.closedBall (F.center i) (F.radius i + 2 * a) → C.eval β x = ρ)

theorem geometry_regular
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    S.regular (geometry C F R hpolar ha hρ β hβ0 hβle hplateau).fluid := by
  let G := geometry C F R hpolar ha hρ β hβ0 hβle hplateau
  apply (D.regular_iff _).2
  apply G.sqrt_fluid_mem hρ D.H1 (fun i => RadialCollar.root (F.center i) (F.radius i) a)
  · intro i x
    exact RadialCollar.root_nonneg _ _ _ _
  · intro i x hx
    exact RadialCollar.root_one_outside ha hx
  · intro i x hx
    apply RadialCollar.root_zero ha
    change dist x (F.center i) ≤ F.radius i at hx
    linarith
  · intro i x hx
    change C.eval (R.collar i) x = _
    rw [R.collar_eval i]
    have h := RadialCollar.density_on_shell (ρ := ρ) ha (lt_of_not_ge hx)
    nlinarith
  · exact hβmem
  · intro i
    exact RadialCollar.correction_mem D.H1 D.smooth_mem _ ρ
      (F.radius_pos i) ha (F.collar_room i)

theorem geometry_gradient_identity
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    S.gradient (geometry C F R hpolar ha hρ β hβ0 hβle hplateau).fluid =
      S.gradient β + ∑ i, D.energy (RadialCollar.correction (F.center i) (F.radius i) a ρ) := by
  let G := geometry C F R hpolar ha hρ β hβ0 hβle hplateau
  let profiles : Fin n → Space → ℝ := fun i => RadialCollar.root (F.center i) (F.radius i) a
  have hp_nonneg : ∀ i x, 0 ≤ profiles i x := fun i x => RadialCollar.root_nonneg _ _ _ _
  have hp_outside : ∀ i x, x ∉ G.enlarged i → profiles i x = 1 := by
    intro i x hx
    exact RadialCollar.root_one_outside ha hx
  have hp_core : ∀ i x, x ∈ G.core i → profiles i x = 0 := by
    intro i x hx
    apply RadialCollar.root_zero ha
    change dist x (F.center i) ≤ F.radius i at hx
    linarith
  have hp_collar : ∀ i x, x ∉ G.core i → C.eval (G.collar i) x = ρ * (profiles i x ^ 2 - 1) := by
    intro i x hx
    change C.eval (R.collar i) x = _
    rw [R.collar_eval i]
    have h := RadialCollar.density_on_shell (ρ := ρ) ha (lt_of_not_ge hx)
    dsimp [profiles]
    nlinarith
  have hsqrt : (fun x => Real.sqrt (C.eval G.fluid x)) =
      Gluing.gluedRoot Finset.univ (fun x => Real.sqrt (C.eval β x)) (Real.sqrt ρ) profiles := by
    rw [G.eval_fluid_eq_gluedDensity hρ profiles hp_core hp_collar]
    apply Gluing.sqrt_gluedDensity Finset.univ G.enlarged _ _ profiles
    · intro i _ j _ hij
      exact F.disjoint hij
    · exact fun _ => Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
    · exact fun i _ => hp_nonneg i
    · exact fun i _ => hp_outside i
    · intro i _ x hx
      change Real.sqrt (C.eval β x) = Real.sqrt ρ
      rw [hplateau i x hx]
  have hregular := geometry_regular S D F R hpolar ha hρ β hβ0 hβle hplateau hβmem
  let base : D.H1 := ⟨fun x => Real.sqrt (C.eval β x), hβmem⟩
  let localRoot : Fin n → D.H1 := fun i =>
    ⟨RadialCollar.correction (F.center i) (F.radius i) a ρ,
      RadialCollar.correction_mem D.H1 D.smooth_mem _ ρ (F.radius_pos i) ha (F.collar_room i)⟩
  let fluidRoot : D.H1 :=
    ⟨fun x => Real.sqrt (C.eval G.fluid x), (D.regular_iff _).1 hregular⟩
  have hroots : fluidRoot = base + ∑ i, localRoot i := by
    apply Subtype.ext
    funext x
    have hx := congrFun hsqrt x
    simpa [fluidRoot, base, localRoot, profiles, Gluing.gluedRoot,
      RadialCollar.correction, Finset.sum_apply] using hx
  have hsupp : ∀ i, tsupport ((localRoot i : D.H1) : Space → ℝ) ⊆
      Metric.closedBall (F.center i) (F.radius i + 2 * a) := by
    intro i
    exact Set.Subset.trans (RadialCollar.correction_tsupport_inner _ ρ ha)
      (Metric.closedBall_subset_closedBall (by linarith))
  have hlocal : ∀ i j, i ≠ j → D.form.form (localRoot i) (localRoot j) = 0 := by
    intro i j hij
    exact D.disjoint_locality _ _ ((F.disjoint hij).mono (hsupp i) (hsupp j))
  have hbase_local : ∀ i, D.form.form base (localRoot i) = 0 := by
    intro i
    apply D.constant_locality base (localRoot i)
      (Metric.ball (F.center i) (F.radius i + 2 * a)) (Real.sqrt ρ) Metric.isOpen_ball
    · intro x hx
      have hinner := RadialCollar.correction_tsupport_inner (F.center i) (r := F.radius i) ρ ha hx
      change dist x (F.center i) < F.radius i + 2 * a
      have hd : dist x (F.center i) ≤ F.radius i + 7 * a / 4 := hinner
      linarith
    · intro x hx
      change Real.sqrt (C.eval β x) = Real.sqrt ρ
      rw [hplateau i x (Metric.ball_subset_closedBall hx)]
  have henergy := Gluing.gradient_energy_identity D.form Finset.univ base localRoot
    (fun i _ => hbase_local i) (fun i _ j _ hij => hlocal i j hij)
  have hβregular : S.regular β := (D.regular_iff β).2 hβmem
  rw [D.gradient_eq _ hregular, D.gradient_eq β hβregular]
  change D.energy (fluidRoot : Space → ℝ) = D.energy (base : Space → ℝ) + _
  rw [D.energy_eq fluidRoot, D.energy_eq base, hroots, henergy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (D.energy_eq (localRoot i)).symm

/-- Standard Coulomb representations and radial identities. -/
structure CoulombLaws (C : TrialState.ChargeModel Space V) (sf : ℝ) where
  energy : (Space → ℝ) → ℝ
  potential : (Space → ℝ) → Space → ℝ
  energy_eval : ∀ f : V, C.coulomb.form f f = energy (C.eval f)
  potential_eval : ∀ f : V, C.potential f = potential (C.eval f)
  polar : RadialCollar.PolarLaw C.measure sf
  exterior : RadialCollar.ExteriorNewtonLaw C.measure potential
  field : RadialCollar.NewtonLaw C.measure energy

theorem core_newton [IsFiniteMeasureOnCompacts C.measure]
    (L : CoulombLaws C sf) (z : Space) {r : ℝ} (hr : 0 < r) (ρ : ℝ)
    (d q : V) (hq : C.eval q = RadialCollar.coreBackground z r ρ)
    (hdint : Integrable (C.eval d) C.measure)
    (hsupport : Function.support (C.eval d) ⊆ Metric.closedBall z r)
    (hradial : RadialCollar.RadialAbout z (C.eval d))
    (hneutral : C.mass d = C.mass q) :
    ∀ x, x ∉ Metric.closedBall z r → C.potential (d - q) x = 0 := by
  classical
  rw [L.potential_eval]
  have hqint : Integrable (C.eval q) C.measure := by rw [hq]; exact core_integrable C z r ρ
  have hfint : Integrable (C.eval (d - q)) C.measure := by
    simpa only [map_sub, Pi.sub_apply] using hdint.sub hqint
  have hfradial : RadialCollar.RadialAbout z (C.eval (d - q)) := by
    obtain ⟨profile, hprofile⟩ := hradial
    refine ⟨fun t => profile t - if t ≤ r then ρ else 0, ?_⟩
    intro x
    simp only [map_sub, Pi.sub_apply, hprofile x, hq, RadialCollar.coreBackground]
  have hfsupport : ∀ x, x ∉ Metric.closedBall z r → C.eval (d - q) x = 0 := by
    intro x hx
    have hd0 : C.eval d x = 0 := by
      by_contra hn
      exact hx (hsupport hn)
    have hx' : ¬ dist x z ≤ r := hx
    simp [map_sub, Pi.sub_apply, hd0, hq, RadialCollar.coreBackground, hx']
  have hfneutral : (∫ x, C.eval (d - q) x ∂C.measure) = 0 := by
    rw [← C.mass_integral, map_sub, hneutral, sub_self]
  exact L.exterior z r (C.eval (d - q)) hr hfint hfradial hfsupport hfneutral

theorem core_mass_formula
    {κ : ℝ} (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r →
      C.measure.real (Metric.closedBall z r) = κ * r ^ 3)
    (z : Space) {r : ℝ} (hr : 0 ≤ r) (ρ : ℝ) (q : V)
    (hq : C.eval q = RadialCollar.coreBackground z r ρ) :
    C.mass q = ρ * (κ * r ^ 3) := by
  classical
  have heq : RadialCollar.coreBackground z r ρ =
      (Metric.closedBall z r).indicator (fun _ : Space => ρ) := by
    funext x
    simp [RadialCollar.coreBackground, Set.indicator, Metric.mem_closedBall]
  rw [C.mass_integral, hq, heq, integral_indicator Metric.isClosed_closedBall.measurableSet,
    setIntegral_const, smul_eq_mul, hvolume z r hr]
  ring

/-- The permitted local ball ground-state fact, obtained from the canonical
thermodynamic limit and rotation averaging. There is no global trial estimate
in this interface. -/
def NearGroundBallLaw (κ ρ e ε rstar : ℝ) : Prop :=
  ∀ (z : Space) (r : ℝ) (q : V), rstar ≤ r →
    (∃ N : ℕ, ρ * (κ * r ^ 3) = N) →
    C.eval q = RadialCollar.coreBackground z r ρ →
    ∃ Γ : State,
      Integrable (C.eval (S.density Γ)) C.measure ∧
      Function.support (C.eval (S.density Γ)) ⊆ Metric.closedBall z r ∧
      RadialCollar.RadialAbout z (C.eval (S.density Γ)) ∧
      C.mass (S.density Γ) = C.mass q ∧
      S.jellium Γ q ≤ (e + ε) * (κ * r ^ 3)

/-- Data of fixed local states, retained when the translated family is built. -/
structure CoreData (κ e ε : ℝ) (cores : Fin n → State) : Prop where
  integrable : ∀ i, Integrable (C.eval (S.density (cores i))) C.measure
  support : ∀ i, Function.support (C.eval (S.density (cores i))) ⊆
    Metric.closedBall (F.center i) (F.radius i)
  radial : ∀ i, RadialCollar.RadialAbout (F.center i) (C.eval (S.density (cores i)))
  neutral : ∀ i, C.mass (S.density (cores i)) = C.mass (R.core i)
  upper : ∀ i, S.jellium (cores i) (R.core i) ≤ (e + ε) * (κ * F.radius i ^ 3)

theorem exists_core_data {κ e ε rstar : ℝ}
    (hballs : NearGroundBallLaw (C := C) S κ ρ e ε rstar)
    (hrstar : ∀ i, rstar ≤ F.radius i)
    (hinteger : ∀ i, ∃ N : ℕ, ρ * (κ * F.radius i ^ 3) = N) :
    ∃ cores : Fin n → State, CoreData S F R κ e ε cores := by
  classical
  have hc := fun i => hballs (F.center i) (F.radius i) (R.core i)
    (hrstar i) (hinteger i) (R.core_eval i)
  refine ⟨fun i => Classical.choose (hc i), ?_⟩
  exact ⟨fun i => (Classical.choose_spec (hc i)).1,
    fun i => (Classical.choose_spec (hc i)).2.1,
    fun i => (Classical.choose_spec (hc i)).2.2.1,
    fun i => (Classical.choose_spec (hc i)).2.2.2.1,
    fun i => (Classical.choose_spec (hc i)).2.2.2.2⟩

include ha hρ hβ0 hβle hplateau in
/-- Complete finite trial construction with a fixed, packing-independent
surface constant. The core states are supplied once and can then be translated.
Every fluid hypothesis is derived from the explicit radial profiles. -/
theorem finite_upper_trial [IsFiniteMeasureOnCompacts C.measure]
    (L : CoulombLaws C sf) (hsf : 0 ≤ sf) (hh₂ : 0 ≤ h₂)
    {κ e ε M K : ℝ}
    (hKcost : ∀ (z : Space) (r a ρ : ℝ), 0 < r → 0 < a → 2 * a ≤ r → 0 ≤ ρ →
      D.energy (RadialCollar.correction z r a ρ) ≤ K * ρ * r ^ 2 / a)
    (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r → C.measure.real (Metric.closedBall z r) = κ * r ^ 3)
    (cores : Fin n → State) (hc : CoreData S F R κ e ε cores)
    (hM : 0 < M) (hcap : RadialCollar.amplitude * ρ ≤ M)
    (hβmem : (fun x => Real.sqrt (C.eval β x)) ∈ D.H1) :
    ∃ Γ : State,
      S.density Γ = β + (∑ i, (S.density (cores i) - R.core i)) + ∑ i, R.collar i ∧
      C.mass (S.density Γ) = C.mass β ∧
      S.jellium Γ β ≤
        (e + ε) * (∑ i, κ * F.radius i ^ 3) + h₂ * S.gradient β +
        (h₂ * K * ρ / a + (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) *
          (∑ i, F.radius i ^ 2) +
        h₂ * cTF * M ^ ((2 : ℝ) / 3) *
          (C.mass β - ρ * (∑ i, κ * F.radius i ^ 3)) := by
  classical
  let G := geometry C F R L.polar ha hρ β hβ0 hβle hplateau
  have hregular : S.regular G.fluid :=
    geometry_regular S D F R L.polar ha hρ β hβ0 hβle hplateau hβmem
  have hsupport : ∀ i, Function.support (C.eval (S.density (cores i))) ⊆ G.core i :=
    fun i => hc.support i
  have hcoreNewton : ∀ i x, x ∉ G.core i →
      C.potential (S.density (cores i) - G.coreBackground i) x = 0 := by
    intro i
    exact core_newton L (F.center i) (F.radius_pos i) ρ (S.density (cores i)) (R.core i)
      (R.core_eval i) (hc.integrable i) (hc.support i) (hc.radial i) (hc.neutral i)
  have hcollarNewton : ∀ i x, x ∉ G.enlarged i → C.potential (G.collar i) x = 0 := by
    intro i x hx
    change C.potential (R.collar i) x = 0
    rw [L.potential_eval, R.collar_eval i]
    exact RadialCollar.charge_zero_potential L.polar L.exterior _ ρ
      (F.radius_pos i) ha (F.collar_room i) x hx
  let coreUpper : Fin n → ℝ := fun i => (e + ε) * (κ * F.radius i ^ 3)
  let collarUpper : Fin n → ℝ := fun i =>
    (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * F.radius i ^ 2 * a ^ 3
  have hcollarUpper : ∀ i, C.coulomb.form (G.collar i) (G.collar i) ≤ collarUpper i := by
    intro i
    change C.coulomb.form (R.collar i) (R.collar i) ≤ _
    rw [L.energy_eval, R.collar_eval i]
    exact RadialCollar.coulomb_cost L.polar hsf L.field _ (F.radius_pos i) ha (F.collar_room i) hρ
  obtain ⟨Γ, hΓd, hΓmass, hΓenergy⟩ := S.assemble_upper_trial G cores hρ
    RadialCollar.amplitude_ge_one hM hcap hregular hsupport hcoreNewton hcollarNewton
    (fun i => hc.neutral i) coreUpper collarUpper
    (fun i => hc.upper i) hcollarUpper
  have hgrad := geometry_gradient_identity S D F R L.polar ha hρ β hβ0 hβle hplateau hβmem
  have hlocalcost : (∑ i, D.energy (RadialCollar.correction (F.center i) (F.radius i) a ρ)) ≤
      (K * ρ / a) * (∑ i, F.radius i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := hKcost (F.center i) (F.radius i) a ρ (F.radius_pos i) ha (F.collar_room i) hρ
    calc
      _ ≤ K * ρ * F.radius i ^ 2 / a := h
      _ = _ := by ring
  have hgradient : S.gradient G.fluid ≤ S.gradient β + (K * ρ / a) * (∑ i, F.radius i ^ 2) := by
    rw [hgrad]
    linarith
  have hmass : C.mass G.fluid = C.mass β - ρ * (∑ i, κ * F.radius i ^ 3) := by
    rw [G.fluid_mass, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact core_mass_formula hvolume (F.center i) (F.radius_pos i).le ρ (R.core i) (R.core_eval i)
  have hcoresum : (∑ i, coreUpper i) = (e + ε) * (∑ i, κ * F.radius i ^ 3) := by
    simp [coreUpper, Finset.mul_sum]
  have hcollarsum : (∑ i, collarUpper i) =
      ((8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3) * (∑ i, F.radius i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [collarUpper]
    ring
  refine ⟨Γ, hΓd, hΓmass, ?_⟩
  rw [hmass, hcoresum, hcollarsum] at hΓenergy
  have hgradscaled := mul_le_mul_of_nonneg_left hgradient hh₂
  change S.jellium Γ β ≤ _ at hΓenergy
  calc
    S.jellium Γ β ≤
        (e + ε) * (∑ i, κ * F.radius i ^ 3) +
          (h₂ * S.gradient G.fluid + h₂ * cTF * M ^ ((2 : ℝ) / 3) *
            (C.mass β - ρ * (∑ i, κ * F.radius i ^ 3))) +
          (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3 *
            (∑ i, F.radius i ^ 2) := hΓenergy
    _ ≤ (e + ε) * (∑ i, κ * F.radius i ^ 3) +
          (h₂ * (S.gradient β + K * ρ / a * (∑ i, F.radius i ^ 2)) +
            h₂ * cTF * M ^ ((2 : ℝ) / 3) * (C.mass β - ρ * (∑ i, κ * F.radius i ^ 3))) +
          (8 * sf * RadialCollar.amplitude) ^ 2 * ρ ^ 2 * a ^ 3 *
            (∑ i, F.radius i ^ 2) := by linarith only [hgradscaled]
    _ = _ := by ring

end Jellium.UpperConstruction
