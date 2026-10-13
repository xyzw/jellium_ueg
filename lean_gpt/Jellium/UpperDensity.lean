import Jellium.PeriodicSelected
import Jellium.BaseProfiles
import Jellium.UpperBackground
import Jellium.UpperMixture
import Jellium.CenteredProfiles
import Jellium.JointDensity
import Jellium.Boundary

/-! The actual averaged periodic trial density and its localization lower
bound. Every bounded-layer property is derived from the finite Fock trial,
its neutral base profiles and the actual lattice translation measure. -/

open Set Metric MeasureTheory MeasureTheory.Measure Filter
open scoped Topology
open Classical

namespace Jellium.UpperDensity

open Spatial UpperConstruction MeasurableTrial Jellium.Lattice
abbrev Space := Spatial.Space

universe v w
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
variable {State : Type w} [MeasurableSpace State]
variable (C : TrialState.ChargeModel Space V) {h₂ cTF sf a ρ : ℝ} {m : ℕ}
variable (S : TrialState.StateAPI C State h₂ cTF)
variable (D : SobolevDirichlet C S sf) (F : BallFamily m a)
variable (Reps : LocalRepresentatives C F ρ)

/-- Construction inputs already supplied by the packing, base-core and
smoothed-background constructions. No averaged-density property is included. -/
structure Inputs (L M κ e ε : ℝ) where
  measure_eq : C.measure = volume
  ha : 0 < a
  hρ : 0 ≤ ρ
  hL : 0 < L
  inside : ∀ i, closedBall (F.center i) (F.radius i + 2 * a) ⊆ cube L
  polar : RadialCollar.PolarLaw C.measure sf
  obs : UpperMixture.ObservableLaws C S
  base : Fin m → State
  cores : CoreData S F Reps κ e ε base
  χ : Space → ℝ
  β : ℝ → V
  background : ∀ Rbox, UpperBackground.Data C S D χ ρ Rbox a (β Rbox)
  hM : 0 < M
  cap : RadialCollar.amplitude * ρ ≤ M

variable {C S D F Reps} {L M κ e ε : ℝ}

namespace Inputs

variable (I : Inputs C S D F Reps L M κ e ε)
variable (T : ChargeTranslations C) (A : StateTranslations C S T) (O : FockOperations C S)

noncomputable def shifts (Rbox : ℝ) : Finset LatticeIndex :=
  Coverage.selectionEnvelope L Rbox (L / 2) I.hL

noncomputable def states (Rbox : ℝ) : Space → State :=
  PeriodicSelected.trial S T A O F Reps (I.shifts Rbox) L Rbox M (I.β Rbox) I.base

theorem states_measurable [MeasurableAdd₂ V] [MeasurableSub₂ V] (Rbox : ℝ) :
    Measurable (I.states T A O Rbox) :=
  PeriodicSelected.trial_measurable S T A O F Reps (I.shifts Rbox) L Rbox M
    (I.β Rbox) I.base I.ha.le

noncomputable def average (Rbox : ℝ) (x : Space) : ℝ :=
  ∫ u, C.eval (S.density (I.states T A O Rbox u)) x ∂shiftMeasure L

noncomputable def correction (i : Fin m) : Space → ℝ :=
  C.eval (S.density (I.base i) - Reps.core i + Reps.collar i)

/- The inserted zero gives the same maximum for every nonempty packing and
also makes the definition meaningful for the empty finite family. -/
noncomputable def radiusMax (_I : Inputs C S D F Reps L M κ e ε) : ℝ :=
  (insert 0 (Finset.univ.image F.radius)).sup' (by simp) id

noncomputable def width : ℝ := a + 2 * (I.radiusMax + 2 * a)

omit [MeasurableSpace V] in
/-- The layer width in the revised upper proof. -/
theorem width_eq : I.width = 5 * a + 2 * I.radiusMax := by
  unfold width
  ring

noncomputable def bound : ℝ := RadialCollar.amplitude * ρ +
  (L ^ 3)⁻¹ * ∑ i, ∫ x, C.eval (S.density (I.base i)) x

noncomputable def fluid (Rbox : ℝ) (u x : Space) : ℝ :=
  C.eval (MeasurableTrial.fluid (I.β Rbox) (PeriodicSelected.selection F (I.shifts Rbox) L Rbox)
    (PeriodicSelected.coreCharge T F Reps (I.shifts Rbox) L)
    (PeriodicSelected.collarCharge T F Reps (I.shifts Rbox) L) u) x

include I in
omit [MeasurableSpace V] in
theorem enlarged_nonneg (i : Fin m) : 0 ≤ F.radius i + 2 * a := by
  have := F.radius_pos i
  have := I.ha
  linarith

omit [MeasurableSpace V] in
theorem radiusMax_nonneg : 0 ≤ I.radiusMax :=
  Finset.le_sup' id (Finset.mem_insert_self _ _)

omit [MeasurableSpace V] in
theorem radius_le_max (i : Fin m) : F.radius i ≤ I.radiusMax :=
  Finset.le_sup' id (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

omit [MeasurableSpace V] in
theorem enlarged_le (i : Fin m) : F.radius i + 2 * a ≤ I.radiusMax + 2 * a :=
  add_le_add (I.radius_le_max i) le_rfl

omit [MeasurableSpace V] in
theorem width_nonneg : 0 ≤ I.width := by
  have := I.radiusMax_nonneg
  have := I.ha
  dsimp [width]
  linarith

omit [MeasurableSpace V] in
theorem a_le_width : a ≤ I.width := by
  have := I.radiusMax_nonneg
  have := I.ha
  dsimp [width]
  linarith

include I in
omit [MeasurableSpace V] in
theorem center_bound (i : Fin m) (k : Fin 3) : |F.center i k| ≤ L / 2 :=
  (I.inside i (mem_closedBall_self (I.enlarged_nonneg i)) k).le

omit [MeasurableSpace V] in
theorem correction_integrable (i : Fin m) : Integrable (I.correction i) := by
  let : IsFiniteMeasureOnCompacts C.measure := by rw [I.measure_eq]; infer_instance
  rw [← I.measure_eq]
  exact BaseProfiles.correction_integrable S F Reps I.base I.cores I.polar I.ha i

omit [MeasurableSpace V] in
theorem correction_neutral (i : Fin m) : (∫ x, I.correction i x) = 0 := by
  rw [← I.measure_eq]
  exact BaseProfiles.correction_neutral S F Reps I.base I.cores I.polar I.ha i

omit [MeasurableSpace V] in
theorem correction_support (i : Fin m) : Function.support (I.correction i) ⊆
    closedBall (F.center i) (F.radius i + 2 * a) :=
  BaseProfiles.correction_support S F Reps I.base I.cores I.ha i

omit [MeasurableSpace V] in
theorem base_integrable (i : Fin m) : Integrable (C.eval (S.density (I.base i))) := by
  rw [← I.measure_eq]
  exact I.cores.integrable i

omit [MeasurableSpace V] in
theorem background_integrable (Rbox : ℝ) : Integrable (C.eval (I.β Rbox)) := by
  rw [← I.measure_eq]
  exact (I.background Rbox).integrable

theorem trial_density (Rbox : ℝ) (u : Space) :
    S.density (I.states T A O Rbox u) = I.β Rbox +
      (∑ j, if PeriodicSelected.selection F (I.shifts Rbox) L Rbox j u then
        S.density (PeriodicSelected.coreState S T A (I.shifts Rbox) L I.base j u) -
          PeriodicSelected.coreCharge T F Reps (I.shifts Rbox) L j u else 0) +
      ∑ j, if PeriodicSelected.selection F (I.shifts Rbox) L Rbox j u then
        PeriodicSelected.collarCharge T F Reps (I.shifts Rbox) L j u else 0 :=
  PeriodicSelected.trial_density S D T A O F Reps (I.shifts Rbox) I.hL I.inside
    I.polar I.ha I.hρ I.base I.cores.support I.hM I.cap Rbox (I.β Rbox)
    (fun x => ((I.background Rbox).bounds x).1) (fun x => ((I.background Rbox).bounds x).2)
    (I.background Rbox).plateau (I.background Rbox).root_mem u

theorem density_formula (Rbox : ℝ) (u x : Space) :
    C.eval (S.density (I.states T A O Rbox u)) x = C.eval (I.β Rbox) x +
      ∑ i, ∑ z ∈ I.shifts Rbox, selectedCorrection (cube Rbox) a
        (F.center i + latticeShift L z + u) (F.radius i + 2 * a)
        (fun y => I.correction i (y - latticeShift L z - u)) x :=
  PeriodicSelected.density_formula S T A O F Reps (I.shifts Rbox) L Rbox M (I.β Rbox)
    I.base u (I.trial_density T A O Rbox u) x

theorem density_core_fluid (Rbox : ℝ) (u x : Space) :
    C.eval (S.density (I.states T A O Rbox u)) x = I.fluid T Rbox u x +
      ∑ i, ∑ z ∈ I.shifts Rbox, selectedCorrection (cube Rbox) a
        (F.center i + latticeShift L z + u) (F.radius i + 2 * a)
        (fun y => C.eval (S.density (I.base i)) (y - latticeShift L z - u)) x :=
  PeriodicSelected.density_core_fluid S T A O F Reps (I.shifts Rbox) L Rbox M (I.β Rbox)
    I.base u (I.trial_density T A O Rbox u) x

theorem fluid_bounds (Rbox : ℝ) (u x : Space) :
    0 ≤ I.fluid T Rbox u x ∧ I.fluid T Rbox u x ≤ RadialCollar.amplitude * ρ :=
  PeriodicSelected.fluid_bound T F Reps (I.shifts Rbox) I.hL I.inside I.polar I.ha I.hρ
    Rbox (I.β Rbox) (fun x => ((I.background Rbox).bounds x).1)
    (fun x => ((I.background Rbox).bounds x).2) (I.background Rbox).plateau u x

theorem joint_integrable (Rbox : ℝ) :
    Integrable (fun p : Space × Space => C.eval (S.density (I.states T A O Rbox p.1)) p.2)
      ((shiftMeasure L).prod C.measure) := by
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability I.hL
  rw [I.measure_eq]
  apply JointDensity.integrable_of_centered_density_identity (shiftMeasure L) I.ha.le
    Finset.univ (I.shifts Rbox) F.center (fun i => F.radius i + 2 * a)
    (C.eval (I.β Rbox)) I.correction (fun u x => C.eval (S.density (I.states T A O Rbox u)) x)
    (I.background_integrable Rbox) (fun i _ => I.enlarged_nonneg i)
    (fun i _ => I.correction_integrable i)
  exact Filter.Eventually.of_forall (fun p => I.density_formula T A O Rbox p.1 p.2)

theorem average_integrable (Rbox : ℝ) : Integrable (I.average T A O Rbox) C.measure := by
  let : SFinite C.measure := by rw [I.measure_eq]; infer_instance
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability I.hL
  exact (I.joint_integrable T A O Rbox).integral_prod_right

theorem parameter_integrable (Rbox : ℝ) (x : Space) :
    Integrable (fun u => C.eval (S.density (I.states T A O Rbox u)) x) (shiftMeasure L) := by
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability I.hL
  have h := (integrable_const (C.eval (I.β Rbox) x)).add
    (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum (I.shifts Rbox) fun z _ =>
      CenteredProfiles.integrable_selected I.hL Rbox a (F.radius i + 2 * a) (F.center i) x z
        (I.correction i) I.ha.le (I.enlarged_nonneg i) (I.correction_integrable i))
  exact h.congr (Filter.Eventually.of_forall (fun u => (I.density_formula T A O Rbox u x).symm))

omit [MeasurableSpace V] in
theorem core_parameter_integrable (Rbox : ℝ) (x : Space) :
    Integrable (fun u => ∑ i, ∑ z ∈ I.shifts Rbox, selectedCorrection (cube Rbox) a
      (F.center i + latticeShift L z + u) (F.radius i + 2 * a)
      (fun y => C.eval (S.density (I.base i)) (y - latticeShift L z - u)) x) (shiftMeasure L) :=
  integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum (I.shifts Rbox) fun z _ =>
    CenteredProfiles.integrable_selected I.hL Rbox a (F.radius i + 2 * a) (F.center i) x z
      (C.eval (S.density (I.base i))) I.ha.le (I.enlarged_nonneg i) (I.base_integrable i)

include A O in
theorem fluid_parameter_integrable (Rbox : ℝ) (x : Space) :
    Integrable (fun u => I.fluid T Rbox u x) (shiftMeasure L) := by
  apply ((I.parameter_integrable T A O Rbox x).sub (I.core_parameter_integrable Rbox x)).congr
  apply Filter.Eventually.of_forall
  intro u
  have h := I.density_core_fluid T A O Rbox u x
  dsimp only [Pi.sub_apply]
  linarith

theorem average_bounds (Rbox : ℝ) (x : Space) :
    0 ≤ I.average T A O Rbox x ∧ I.average T A O Rbox x ≤ I.bound := by
  let : IsProbabilityMeasure (shiftMeasure L) := shiftMeasure_probability I.hL
  refine ⟨integral_nonneg (fun u => I.obs.density_nonnegative _ x), ?_⟩
  unfold average
  simp_rw [I.density_core_fluid T A O Rbox]
  rw [integral_add (I.fluid_parameter_integrable T A O Rbox x) (I.core_parameter_integrable Rbox x)]
  have hf : (∫ u, I.fluid T Rbox u x ∂shiftMeasure L) ≤ RadialCollar.amplitude * ρ := by
    calc
      _ ≤ ∫ _u, RadialCollar.amplitude * ρ ∂shiftMeasure L :=
        integral_mono (I.fluid_parameter_integrable T A O Rbox x) (integrable_const _)
          (fun u => (I.fluid_bounds T Rbox u x).2)
      _ = _ := by simp
  apply add_le_add hf
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum (I.shifts Rbox) fun z _ =>
    CenteredProfiles.integrable_selected I.hL Rbox a (F.radius i + 2 * a) (F.center i) x z
      (C.eval (S.density (I.base i))) I.ha.le (I.enlarged_nonneg i) (I.base_integrable i)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact CenteredProfiles.selected_average_le I.hL (I.shifts Rbox) x (F.center i)
    (C.eval (S.density (I.base i))) I.ha.le (I.enlarged_nonneg i) (I.base_integrable i)
    (I.obs.density_nonnegative _) ((I.cores.support i).trans
      (closedBall_subset_closedBall (by have := I.ha; linarith)))

omit [MeasurableSpace V] in
/-- Neutral core masses identify the core contribution to the density cap
with the occupied fraction of one periodic cell. -/
theorem bound_eq_coverage
    (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r →
      C.measure.real (closedBall z r) = κ * r ^ 3) :
    I.bound = RadialCollar.amplitude * ρ +
      ρ * ((∑ i, κ * F.radius i ^ 3) / L ^ 3) := by
  have hmass (i : Fin m) : (∫ x, C.eval (S.density (I.base i)) x) =
      ρ * (κ * F.radius i ^ 3) := by
    rw [← I.measure_eq, ← C.mass_integral, I.cores.neutral i]
    exact UpperConstruction.core_mass_formula hvolume (F.center i)
      (F.radius_pos i).le ρ (Reps.core i) (Reps.core_eval i)
  unfold bound
  simp_rw [hmass]
  rw [← Finset.mul_sum]
  ring

/-- The revised proof's density cap is independent of the finite packing. -/
theorem average_uniform_bounds
    (hvolume : ∀ (z : Space) (r : ℝ), 0 ≤ r →
      C.measure.real (closedBall z r) = κ * r ^ 3)
    (hcoverage : (∑ i, κ * F.radius i ^ 3) / L ^ 3 ≤ 1)
    (Rbox : ℝ) (x : Space) :
    0 ≤ I.average T A O Rbox x ∧
      I.average T A O Rbox x ≤ (RadialCollar.amplitude + 1) * ρ := by
  obtain ⟨hzero, hbound⟩ := I.average_bounds T A O Rbox x
  refine ⟨hzero, hbound.trans ?_⟩
  rw [I.bound_eq_coverage hvolume]
  have h := mul_le_mul_of_nonneg_left hcoverage I.hρ
  nlinarith

theorem average_plateau (Rbox : ℝ) (x : Space) (hx : x ∈ cube (Rbox - 2 * I.width)) :
    I.average T A O Rbox x = ρ := by
  have hβ : C.eval (I.β Rbox) x = ρ :=
    (I.background Rbox).plateau x (cube_mono (by linarith [I.a_le_width]) hx)
  have hcover (i : Fin m) (_ : i ∈ Finset.univ) (z : LatticeIndex) (u : Space)
      (hu : u ∈ fundamentalCube L)
      (hsel : selectedBall (cube Rbox) a (F.center i + latticeShift L z + u) (F.radius i + 2 * a)) :
      z ∈ I.shifts Rbox :=
    Coverage.selectionEnvelope_contains I.hL I.ha.le (I.enlarged_nonneg i) (I.center_bound i) hu hsel
  have h := CenteredProfiles.neutral_plateau (ρ₀ := ρ) I.hL Finset.univ (I.shifts Rbox)
    F.center (fun i => F.radius i + 2 * a) I.correction
    (fun i _ => I.enlarged_le i) (fun i _ => I.correction_integrable i)
    (fun i _ => I.correction_support i) (fun i _ => I.correction_neutral i) hcover x hx
  unfold average
  simp_rw [I.density_formula T A O Rbox, hβ]
  exact h

theorem average_support (Rbox : ℝ) : Function.support (I.average T A O Rbox) ⊆
    cube (Rbox + 2 * I.width) := by
  intro x hx
  by_contra hout
  have hβ : C.eval (I.β Rbox) x = 0 := by
    by_contra hn
    exact hout (cube_mono (by linarith [I.a_le_width]) ((I.background Rbox).support hn))
  have hxR : x ∉ cube Rbox := fun h => hout (cube_mono (by linarith [I.width_nonneg]) h)
  have hzero (u : Space) (i : Fin m) (z : LatticeIndex) :
      selectedCorrection (cube Rbox) a (F.center i + latticeShift L z + u) (F.radius i + 2 * a)
        (fun y => I.correction i (y - latticeShift L z - u)) x = 0 :=
    CenteredProfiles.selected_vanishes_outside I.ha.le (F.center i) x u z
      (I.correction i) (I.correction_support i) hxR
  apply hx
  unfold average
  simp_rw [I.density_formula T A O Rbox, hβ, hzero]
  simp

/-- All bounded-layer properties of the actual averaged family. -/
structure Properties : Prop where
  joint : ∀ Rbox, Integrable
    (fun p : Space × Space => C.eval (S.density (I.states T A O Rbox p.1)) p.2)
    ((shiftMeasure L).prod C.measure)
  integrable : ∀ Rbox, Integrable (I.average T A O Rbox) C.measure
  bounds : ∀ Rbox x, 0 ≤ I.average T A O Rbox x ∧ I.average T A O Rbox x ≤ I.bound
  support : ∀ Rbox, Function.support (I.average T A O Rbox) ⊆ cube (Rbox + 2 * I.width)
  plateau : ∀ Rbox x, x ∈ cube (Rbox - 2 * I.width) → I.average T A O Rbox x = ρ

theorem properties : I.Properties T A O :=
  ⟨I.joint_integrable T A O, I.average_integrable T A O, I.average_bounds T A O,
    I.average_support T A O, I.average_plateau T A O⟩

end Inputs

/-- Standard localization facts for arbitrary represented, bounded compact
densities. The representation premise excludes the empty constrained search.
The structure contains no bounded-layer or thermodynamic lower conclusion. -/
structure LocalizationLaws (C : TrialState.ChargeModel Space V)
    (S : TrialState.StateAPI C State h₂ cTF)
    {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (ρ₀ eU : ℝ) where
  diameter : ℝ → ℝ
  cellVolume : ℝ → ℝ
  cellEnergy : ℝ → ℝ
  diameter_nonneg : ∀ l, 0 ≤ diameter l
  cellVolume_pos : ∀ l, 0 < cellVolume l
  loConstant : ℝ
  loConstant_nonneg : 0 ≤ loConstant
  localizationConstant : ℝ
  densityCost : ℝ
  densityCost_nonneg : 0 ≤ densityCost
  tiling : ∀ l Rbox width, U → Boundary.WindowTiling Rbox width (diameter l) (cellVolume l)
  cell_limit : Tendsto (fun l => cellEnergy l / cellVolume l) atTop (𝓝 eU)
  cell_value : ∀ l Rbox width u i, i ∈ (tiling l Rbox width u).indices →
    Variational.indirectEnergy C S (fun x => ρ₀ * (tiling l Rbox width u).cutoff i x) = cellEnergy l
  local_estimates : ∀ l Rbox width (p : Space → ℝ) B, 0 ≤ width →
    (∃ Γ, Variational.realizes C S Γ p) → Integrable p C.measure →
    (∀ x, 0 ≤ p x ∧ p x ≤ B) → HasCompactSupport p →
    Function.support p ⊆ cube (Rbox + 2 * width) →
    (∀ u i, i ∈ (tiling l Rbox width u).indices →
      Integrable (fun x => ((tiling l Rbox width u).cutoff i x * p x) ^ ((4 : ℝ) / 3))) ∧
    (∀ u i, i ∈ (tiling l Rbox width u).indices →
      -loConstant * (∫ x, ((tiling l Rbox width u).cutoff i x * p x) ^ ((4 : ℝ) / 3)) ≤
        Variational.indirectEnergy C S (fun x => (tiling l Rbox width u).cutoff i x * p x)) ∧
    Integrable (fun u => (tiling l Rbox width u).localSum (Variational.indirectEnergy C S) p) μ
  localization : ∀ᶠ l in atTop, ∀ Rbox width (p : Space → ℝ) B, 0 ≤ width →
    (∃ Γ, Variational.realizes C S Γ p) → Integrable p C.measure →
    (∀ x, 0 ≤ p x ∧ p x ≤ B) → HasCompactSupport p →
    Function.support p ⊆ cube (Rbox + 2 * width) →
    (1 - localizationConstant / l) *
      (∫ u, (tiling l Rbox width u).localSum (Variational.indirectEnergy C S) p ∂μ) -
        densityCost / l * (∫ x, p x + (p x) ^ 2) ≤ Variational.indirectEnergy C S p

namespace Inputs

variable (I : Inputs C S D F Reps L M κ e ε)
variable (T : ChargeTranslations C) (A : StateTranslations C S T) (O : FockOperations C S)

/-- The bounded-layer lower estimate for the actual averaged trial density.
All geometric density hypotheses are discharged by the construction above.
Representability is supplied by the ordinary continuum mixture theorem. -/
theorem localized_lower_bound {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {eU : ℝ}
    (laws : LocalizationLaws C S μ ρ eU)
    (hrepresented : ∀ Rbox, ∃ Γ, Variational.realizes C S Γ (I.average T A O Rbox))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Rbox in atTop, eU - η ≤
      Variational.indirectEnergy C S (I.average T A O Rbox) / Rbox ^ 3 := by
  have hcompact (Rbox : ℝ) : HasCompactSupport (I.average T A O Rbox) :=
    SmoothCube.compactSupport_of_cube_support (I.average_support T A O Rbox)
  have hlocal (l Rbox : ℝ) := laws.local_estimates l Rbox I.width
    (I.average T A O Rbox) I.bound I.width_nonneg (hrepresented Rbox)
    (I.average_integrable T A O Rbox) (I.average_bounds T A O Rbox)
    (hcompact Rbox) (I.average_support T A O Rbox)
  apply Boundary.bounded_layer_from_standard_localization (C := laws.localizationConstant) μ (Variational.indirectEnergy C S)
    (I.average T A O) (fun _ => I.width) laws.diameter laws.cellVolume laws.cellEnergy
    (fun l Rbox => laws.tiling l Rbox I.width)
    (fun _ => I.width_nonneg) laws.diameter_nonneg laws.cellVolume_pos
    laws.loConstant_nonneg laws.densityCost_nonneg (by norm_num : 1 ≤ (4 : ℝ) / 3)
    _ laws.cell_limit (I.average_bounds T A O) (I.average_support T A O)
    (I.average_plateau T A O) (fun l Rbox => (hlocal l Rbox).1)
    (fun l Rbox => (hlocal l Rbox).2.1)
    (fun l Rbox => laws.cell_value l Rbox I.width)
    (fun l Rbox => (hlocal l Rbox).2.2) _ η hη
  · simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun Rbox : ℝ => Rbox⁻¹) atTop (𝓝 (0 : ℝ))).const_mul I.width
  · filter_upwards [laws.localization] with l hl
    exact Filter.Eventually.of_forall (fun Rbox => hl Rbox I.width (I.average T A O Rbox) I.bound
      I.width_nonneg (hrepresented Rbox) (I.average_integrable T A O Rbox)
      (I.average_bounds T A O Rbox) (hcompact Rbox) (I.average_support T A O Rbox))

end Inputs

end Jellium.UpperDensity
