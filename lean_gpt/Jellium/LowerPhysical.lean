import Jellium.InnerDensity
import Jellium.Neutralization
import Jellium.Variational
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Direct physical lower comparison. A smoothed inner-ball UEG state supplies
one confined particle-number sector. The proved neutral completion lemma
then gives a neutral canonical ball, to which the ordinary LN limit applies.
There is no prescribed mean, density dilation, or multi-ball assignment. -/

open Set Metric MeasureTheory Filter Topology

namespace Jellium.LowerPhysical

open Contraction LowerDensity Domains

abbrev Space := Contraction.Space

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℝ V] {State : Type v}
variable (C : TrialState.ChargeModel Space V) {h₂ cTF : ℝ}
variable (S : TrialState.StateAPI C State h₂ cTF)

def coulombPart (Γ : State) : ℝ :=
  S.repulsion Γ - C.coulomb.form (S.density Γ) (S.density Γ)

theorem indirect_decomposition (Γ : State) :
    S.indirect Γ = h₂ * S.kinetic Γ + coulombPart C S Γ := by
  unfold TrialState.StateAPI.indirect CoulombForm.indirect coulombPart
  ring

/-- Ordinary particle-number sector decomposition for a confined state.
No mean-particle-number condition is imposed. -/
structure SectorData (background : Set Space → V)
    (confined : ℝ → ℕ → State → Prop) (R : ℝ) (Γ : State) where
  weight : ℕ → ℝ
  sector : ℕ → State
  nonnegative : ∀ k, 0 ≤ weight k
  summable : Summable weight
  energy_summable : Summable (fun k => weight k *
    S.jellium (sector k) (background (ball 0 R)))
  mass : ∑' k, weight k = 1
  energy : ∑' k, weight k * S.jellium (sector k) (background (ball 0 R)) =
    S.jellium Γ (background (ball 0 R))
  admissible : ∀ k, 0 < weight k → confined R k (sector k)

/-- Actual constrained canonical ball energy, also for nonneutral sectors. -/
noncomputable def ballEnergy (background : Set Space → V)
    (confined : ℝ → ℕ → State → Prop) (R : ℝ) (N : ℕ) : ℝ :=
  Variational.canonicalEnergy C S (confined R N) (background (ball 0 R))

/-- General literature and physical state-space inputs. Neutral completion
is derived from the shell primitives, rather than assumed as a new limit. -/
structure StandardLaws {A : ℝ} (χ : Mollifier A) (ρ eU eJ : ℝ) where
  measure_eq : C.measure = volume
  mollifier_radial : ∃ f : ℝ → ℝ, ∀ x, χ.value x = f ‖x‖
  background : Set Space → V
  background_eval : ∀ Ω, MeasurableSet Ω → Bornology.IsBounded Ω →
    C.eval (background Ω) = Ω.indicator (fun _ => ρ)
  confined : ℝ → ℕ → State → Prop
  kinetic_nonnegative : ∀ Γ, 0 ≤ S.kinetic Γ
  lo_constant : ℝ
  lo_nonnegative : 0 ≤ lo_constant
  lieb_oxford : ∀ (Γ : State) (p : Space → ℝ),
    Variational.realizes C S Γ p → Integrable p →
    (∀ x, 0 ≤ p x ∧ p x ≤ ρ) →
    -lo_constant * ρ ^ ((1 : ℝ) / 3) * (∫ x, p x) ≤ coulombPart C S Γ
  representable : ∀ R d : ℝ, 0 < R → 0 < d →
    ∃ Γ : State, Variational.realizes C S Γ (smoothBall ρ R (scaledKernel χ d))
  ueg : ∀ (R d : ℕ → ℝ), (∀ j, 0 < R j) → (∀ j, 0 < d j) →
    Tendsto R atTop atTop → Tendsto (fun j => d j / R j) atTop (𝓝 0) →
    Tendsto (fun j => d j * R j) atTop atTop →
    Tendsto (fun j => Variational.indirectEnergy C S
      (smoothBall ρ (R j) (scaledKernel χ (d j))) / ballVolume (R j)) atTop (𝓝 eU)
  coulombEnergy : (Space → ℝ) → ℝ
  coulomb_eval : ∀ f : V, coulombEnergy (C.eval f) = C.coulomb.form f f
  coulomb_ae : ∀ f g : Space → ℝ, f =ᵐ[volume] g → coulombEnergy f = coulombEnergy g
  sector_decomposition : ∀ (Γ : State) (p : Space → ℝ) (R r : ℝ),
    0 < R → r < R → Variational.realizes C S Γ p →
    Function.support p ⊆ ball 0 r → SectorData C S background confined R Γ
  stability : ∀ (R : ℝ) (N : ℕ), 0 < R →
    ∃ B : ℝ, ∀ Γ : State, confined R N Γ →
      B ≤ S.jellium Γ (background (ball 0 R))
  neutralization : Neutralization.StandardLaws
    (fun R Γ => S.jellium Γ (background (ball 0 R))) confined ρ
  ln : ∀ (R : ℕ → ℝ) (N : ℕ → ℕ), (∀ j, 0 < R j) →
    Tendsto R atTop atTop → (∀ j, ρ * ballVolume (R j) = (N j : ℝ)) →
    Tendsto (fun j => ballEnergy C S background confined (R j) (N j) /
      ballVolume (R j)) atTop (𝓝 eJ)

variable {C S} {A ρ eU eJ : ℝ} {χ : Mollifier A}

theorem jellium_identity (laws : StandardLaws C S χ ρ eU eJ)
    (Γ : State) (p : Space → ℝ) (R : ℝ) (hp : Variational.realizes C S Γ p) :
    S.jellium Γ (laws.background (ball 0 R)) = S.indirect Γ +
      laws.coulombEnergy (fun x => p x - sharpBall ρ R x) := by
  rw [TrialState.StateAPI.jellium, C.coulomb.jellium_eq_indirect_add_charge]
  change S.indirect Γ + _ = _
  rw [← laws.coulomb_eval]
  congr 1
  apply laws.coulomb_ae
  have hp' : C.eval (S.density Γ) =ᵐ[volume] p := by
    simpa only [Variational.realizes, laws.measure_eq] using hp
  filter_upwards [hp'] with x hx
  simp only [map_sub, Pi.sub_apply, laws.background_eval _ measurableSet_ball isBounded_ball, sharpBall]
  rw [hx]

/-- A probability average has a supported sector no higher than the average.
The proof includes countably many sectors and allows either energy sign. -/
theorem exists_sector_le (laws : StandardLaws C S χ ρ eU eJ)
    {R : ℝ} {Γ : State} (data : SectorData C S laws.background laws.confined R Γ) :
    ∃ N : ℕ, laws.confined R N (data.sector N) ∧
      S.jellium (data.sector N) (laws.background (ball 0 R)) ≤
        S.jellium Γ (laws.background (ball 0 R)) := by
  classical
  let E := S.jellium Γ (laws.background (ball 0 R))
  let e := fun k => S.jellium (data.sector k) (laws.background (ball 0 R))
  have hpositive : ∃ k, 0 < data.weight k := by
    by_contra! h
    have hz (k : ℕ) : data.weight k = 0 := le_antisymm (h k) (data.nonnegative k)
    have hm := data.mass
    simp_rw [hz] at hm
    simp at hm
  obtain ⟨k, hk⟩ := hpositive
  have hex : ∃ k, 0 < data.weight k ∧ e k ≤ E := by
    by_contra! h
    have hle (i : ℕ) : data.weight i * E ≤ data.weight i * e i := by
      by_cases hi : 0 < data.weight i
      · exact mul_le_mul_of_nonneg_left (h i hi).le (data.nonnegative i)
      · have hz : data.weight i = 0 := le_antisymm (le_of_not_gt hi) (data.nonnegative i)
        simp [hz]
    have hlt := Summable.tsum_lt_tsum hle
      (mul_lt_mul_of_pos_left (h k hk) hk) (data.summable.mul_right E) data.energy_summable
    rw [tsum_mul_right, data.mass, one_mul, data.energy] at hlt
    exact (lt_irrefl E) hlt
  obtain ⟨N, hN, he⟩ := hex
  exact ⟨N, data.admissible N hN, he⟩

/-- The inner-ball UEG sequence already has a strict Dirichlet support margin.
Its missing background mass has vanishing energy per unit volume. -/
theorem exists_trial_sequence (laws : StandardLaws C S χ ρ eU eJ)
    (hρ : 0 < ρ) (hh₂ : 0 < h₂) (hA : 0 < A)
    {B : ℝ} (coulomb : CoulombInterpolation laws.coulombEnergy B) (hB : 0 ≤ B) :
    ∃ Γ : ℕ → State,
      (∀ j, Variational.realizes C S (Γ j) (InnerDensity.density χ ρ j)) ∧
      Tendsto (fun j => S.jellium (Γ j)
        (laws.background (ball 0 (InnerDensity.outerRadius A j))) /
        ballVolume (InnerDensity.outerRadius A j)) atTop (𝓝 eU) := by
  classical
  let V₀ : ℕ → ℝ := fun j => ballVolume (InnerDensity.innerRadius j)
  let K := laws.lo_constant * ρ ^ ((1 : ℝ) / 3) * ρ
  have hV (j : ℕ) : 0 < V₀ j := by
    dsimp [V₀, ballVolume]
    have := InnerDensity.innerRadius_pos j
    positivity
  have hlo (j : ℕ) (Φ : State) (hΦ : Variational.realizes C S Φ (InnerDensity.density χ ρ j)) :
      -K * V₀ j ≤ coulombPart C S Φ := by
    have h := laws.lieb_oxford Φ _ hΦ (InnerDensity.density_integrable χ ρ j)
      (InnerDensity.density_bounds χ hρ.le j)
    rw [InnerDensity.density_mass] at h
    dsimp [K, V₀]
    nlinarith only [h]
  have hstable (j : ℕ) : ∃ L : ℝ, ∀ Φ : State,
      Variational.realizes C S Φ (InnerDensity.density χ ρ j) → L ≤ S.indirect Φ := by
    refine ⟨-K * V₀ j, ?_⟩
    intro Φ hΦ
    rw [indirect_decomposition]
    have h := hlo j Φ hΦ
    have hT := mul_nonneg hh₂.le (laws.kinetic_nonnegative Φ)
    linarith only [h, hT]
  have hrepr (j : ℕ) : ∃ Φ : State, Variational.realizes C S Φ (InnerDensity.density χ ρ j) :=
    laws.representable _ _ (InnerDensity.innerRadius_pos j) (InnerDensity.width_pos j)
  have hex (j : ℕ) := Variational.exists_indirect_near_inf C S (hrepr j) (hstable j)
    (div_pos (hV j) (by positivity : (0 : ℝ) < (j : ℝ) + 1))
  choose Γ hΓ hnear using hex
  have hUEG : Tendsto (fun j => Variational.indirectEnergy C S (InnerDensity.density χ ρ j) / V₀ j)
      atTop (𝓝 eU) :=
    laws.ueg InnerDensity.innerRadius InnerDensity.width InnerDensity.innerRadius_pos
      InnerDensity.width_pos InnerDensity.innerRadius_tendsto
      InnerDensity.smoothing_ratio_tendsto InnerDensity.smoothing_product_tendsto
  have hupper : Tendsto (fun j => Variational.indirectEnergy C S (InnerDensity.density χ ρ j) / V₀ j +
      1 / ((j : ℝ) + 1)) atTop (𝓝 eU) := by
    simpa only [add_zero] using hUEG.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hΓenergy : Tendsto (fun j => S.indirect (Γ j) / V₀ j) atTop (𝓝 eU) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hUEG hupper
    · intro j
      exact div_le_div_of_nonneg_right
        (Variational.indirectEnergy_le C S (Γ j) (hΓ j) (hstable j)) (hV j).le
    · intro j
      have he := div_le_div_of_nonneg_right (hnear j).le (hV j).le
      rw [add_div, div_right_comm (V₀ j) ((j : ℝ) + 1) (V₀ j), div_self (ne_of_gt (hV j))] at he
      exact he
  have hdisc := InnerDensity.discrepancy_coulomb_tendsto_zero χ hA.le hρ.le coulomb hB
  have htotal := (hΓenergy.add hdisc).mul (InnerDensity.volume_ratio_tendsto A)
  refine ⟨Γ, hΓ, ?_⟩
  convert htotal using 1
  · funext j
    rw [jellium_identity laws _ _ _ (hΓ j)]
    change (S.indirect (Γ j) + laws.coulombEnergy (InnerDensity.discrepancy χ ρ j)) / _ = _
    dsimp [V₀]
    have hvi : ballVolume (InnerDensity.innerRadius j) ≠ 0 := ne_of_gt (hV j)
    have hvo : ballVolume (InnerDensity.outerRadius A j) ≠ 0 := by
      apply ne_of_gt
      dsimp [ballVolume]
      have hr : 0 < InnerDensity.outerRadius A j :=
        lt_of_lt_of_le zero_lt_one (InnerDensity.outerRadius_one_le hA.le j)
      positivity
    field_simp [hvi, hvo]
  · norm_num

/-- A fixed-width completion does not change the thermodynamic volume. -/
theorem completion_volume_ratio {R T : ℕ → ℝ} {H : ℝ}
    (hRpos : ∀ j, 0 < R j) (hR : Tendsto R atTop atTop)
    (hlo : ∀ j, R j ≤ T j) (hhi : ∀ j, T j ≤ R j + H) :
    Tendsto (fun j => ballVolume (T j) / ballVolume (R j)) atTop (𝓝 1) := by
  have hupper : Tendsto (fun j => 1 + H / R j) atTop (𝓝 1) := by
    simpa only [Function.comp_apply, mul_zero, add_zero, div_eq_mul_inv] using
      (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_inv_atTop_zero.comp hR).const_mul H)
  have hratio : Tendsto (fun j => T j / R j) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro j
      exact (le_div_iff₀ (hRpos j)).2 (by simpa using hlo j)
    · intro j
      apply (div_le_iff₀ (hRpos j)).2
      calc
        T j ≤ R j + H := hhi j
        _ = (1 + H / R j) * R j := by
          rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt (hRpos j))]
  convert hratio.pow 3 using 1
  · funext j
    dsimp [ballVolume]
    field_simp
  · norm_num

/-- Direct lower comparison from the UEG state, a sector below its mean
energy, finite-volume neutral completion, and the canonical ball LN limit. -/
theorem lower_comparison (laws : StandardLaws C S χ ρ eU eJ)
    (hρ : 0 < ρ) (hh₂ : 0 < h₂) (hA : 0 < A)
    {B : ℝ} (coulomb : CoulombInterpolation laws.coulombEnergy B) (hB : 0 ≤ B) :
    eJ ≤ eU := by
  classical
  obtain ⟨Γ, hΓ, henergy⟩ := exists_trial_sequence laws hρ hh₂ hA coulomb hB
  let R₀ := InnerDensity.outerRadius A
  have hR₀ (j : ℕ) : 0 < R₀ j := lt_of_lt_of_le (by norm_num)
    (InnerDensity.outerRadius_one_le hA.le j)
  let data (j : ℕ) : SectorData C S laws.background laws.confined (R₀ j) (Γ j) :=
    laws.sector_decomposition (Γ j) (InnerDensity.density χ ρ j) (R₀ j)
      (InnerDensity.innerRadius j + A * InnerDensity.width j) (hR₀ j)
      (by dsimp [R₀, InnerDensity.outerRadius]
          have := mul_pos hA (InnerDensity.width_pos j)
          linarith)
      (hΓ j) (InnerDensity.density_support χ ρ j)
  choose N hN hsector using fun j => exists_sector_le laws (data j)
  let Φ (j : ℕ) : State := (data j).sector (N j)
  have hlarge : ∀ᶠ j in atTop,
      S.jellium (Γ j) (laws.background (ball 0 (R₀ j))) / ballVolume (R₀ j) ≤ eU + 1 := by
    exact ((tendsto_order.1 henergy).2 (eU + 1) (by linarith)).mono (fun _ h => h.le)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hlarge
  let R (j : ℕ) : ℝ := R₀ (j + j₀)
  have hRpos (j : ℕ) : 0 < R j := hR₀ (j + j₀)
  have hR : Tendsto R atTop atTop :=
    (InnerDensity.outerRadius_tendsto hA.le).comp (tendsto_add_atTop_nat j₀)
  let K : ℝ := (|eU| + 1) * (Real.pi * 4 / 3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound (j : ℕ) :
      S.jellium (Φ (j + j₀)) (laws.background (ball 0 (R j))) ≤ K * R j ^ 3 := by
    have hv : 0 < ballVolume (R j) := by dsimp [ballVolume]; exact mul_pos (by positivity) (pow_pos (hRpos j) _)
    have h := (div_le_iff₀ hv).1 (hj₀ (j + j₀) (Nat.le_add_left j₀ j))
    have he := hsector (j + j₀)
    have hle : eU + 1 ≤ |eU| + 1 := add_le_add (le_abs_self eU) le_rfl
    have hc := mul_le_mul_of_nonneg_right hle hv.le
    dsimp [K]
    dsimp [ballVolume] at h hc
    simpa only [mul_assoc] using he.trans (h.trans hc)
  obtain ⟨H, D, hH, hD, complete⟩ :=
    Neutralization.exists_neutral_completion laws.neutralization hρ K hK
  have hcomplete (j : ℕ) := complete (R j) (N (j + j₀)) (Φ (j + j₀))
    (InnerDensity.outerRadius_one_le hA.le _) (hN (j + j₀)) (hbound j)
  choose T M Ψ hRT hTupper hneutral hΨ hΨenergy using hcomplete
  have hTpos (j : ℕ) : 0 < T j := (hRpos j).trans_le (hRT j)
  have hT : Tendsto T atTop atTop := tendsto_atTop_mono hRT hR
  have hLN := laws.ln T M hTpos hT hneutral
  have hratio := completion_volume_ratio hRpos hR hRT hTupper
  have hleft : Tendsto (fun j => ballEnergy C S laws.background laws.confined (T j) (M j) /
      ballVolume (R j)) atTop (𝓝 eJ) := by
    have h := hLN.mul hratio
    convert h using 1
    · funext j
      have hv : ballVolume (T j) ≠ 0 := ne_of_gt (by dsimp [ballVolume]; exact mul_pos (by positivity) (pow_pos (hTpos j) _))
      field_simp
    · simp only [mul_one]
  have herror : Tendsto (fun j => D * R j ^ 2 / ballVolume (R j)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hR).const_mul (D / (Real.pi * 4 / 3))
    convert h using 1
    · funext j
      dsimp [ballVolume]
      field_simp [ne_of_gt (hRpos j)]
    · simp only [mul_zero]
  have hright := (henergy.comp (tendsto_add_atTop_nat j₀)).add herror
  rw [add_zero] at hright
  apply le_of_tendsto_of_tendsto' hleft hright
  intro j
  have hground := Variational.canonicalEnergy_le C S (Ψ j) (hΨ j)
    (laws.stability (T j) (M j) (hTpos j))
  have he := (hground.trans (hΨenergy j)).trans
    (add_le_add (hsector (j + j₀)) (le_refl (D * R j ^ 2)))
  have hv : 0 ≤ ballVolume (R j) := by
    dsimp [ballVolume]
    exact mul_nonneg (by positivity) (pow_nonneg (hRpos j).le _)
  simpa only [add_div, ballEnergy, R, R₀, Function.comp_apply] using
    div_le_div_of_nonneg_right he hv

end Jellium.LowerPhysical
