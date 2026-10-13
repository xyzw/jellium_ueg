import Jellium.Lattice
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! Joint integrability of the actual translated and selected density family.
The coordinate shear preserves the product of any finite shift measure with
spatial volume. Measurable selection masks and finite sums then give precisely
the joint density integrability needed for continuum mixing and Fubini. -/

open Set MeasureTheory MeasureTheory.Measure
open Classical

namespace Jellium.JointDensity

open Spatial Jellium.Lattice

variable (μ : Measure Space) [IsFiniteMeasure μ]

/-- Joint translation preserves integrability because the map
`(u,x) ↦ (u,x−u)` preserves `μ × volume`. -/
theorem integrable_joint_translate {f : Space → ℝ} (hf : Integrable f)
    (offset : Space) :
    Integrable (fun p : Space × Space => f (p.2 - offset - p.1)) (μ.prod volume) := by
  have hbase := (hf.comp_sub_right offset).comp_snd μ
  have hshear := (measurePreserving_prod_sub μ (volume : Measure Space)).integrable_comp_of_integrable hbase
  convert hshear using 1
  funext p
  congr 1
  exact sub_right_comm p.2 offset p.1

/-- The selected translated profile is jointly integrable, including at
selection boundaries. Its indicator is the pullback of a measurable cube. -/
theorem integrable_joint_selected {L R a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (c : Space) (z : LatticeIndex) {f : Space → ℝ} (hf : Integrable f) :
    Integrable (fun p : Space × Space =>
      selectedCorrection (cube R) a (c + latticeShift L z + p.1) r
        (fun y => f (y - c - latticeShift L z - p.1)) p.2) (μ.prod volume) := by
  have htranslated : Integrable (fun p : Space × Space =>
      f (p.2 - c - latticeShift L z - p.1)) (μ.prod volume) := by
    simpa only [sub_add_eq_sub_sub] using integrable_joint_translate μ hf (c + latticeShift L z)
  exact htranslated.indicator ((measurableSet_selectedBall L R a r c z ha hr).preimage measurable_fst)

theorem integrable_joint_selected_sum {ι : Type*} {L R a : ℝ} (ha : 0 ≤ a)
    (J : Finset ι) (s : Finset LatticeIndex) (c : ι → Space) (r : ι → ℝ)
    (f : ι → Space → ℝ) (hr : ∀ i ∈ J, 0 ≤ r i) (hf : ∀ i ∈ J, Integrable (f i)) :
    Integrable (fun p : Space × Space => ∑ i ∈ J, ∑ z ∈ s,
      selectedCorrection (cube R) a (c i + latticeShift L z + p.1) (r i)
        (fun y => f i (y - c i - latticeShift L z - p.1)) p.2) (μ.prod volume) :=
  integrable_finsetSum J fun i hi => integrable_finsetSum s fun z _ =>
    integrable_joint_selected μ ha (hr i hi) (c i) z (hf i hi)

/-- Joint integrability of a fixed background plus the selected neutral
corrections follows from the integrability of the actual base profiles. -/
theorem integrable_joint_density {ι : Type*} {L R a : ℝ} (ha : 0 ≤ a)
    (J : Finset ι) (s : Finset LatticeIndex) (c : ι → Space) (r : ι → ℝ)
    (β : Space → ℝ) (f : ι → Space → ℝ)
    (hβ : Integrable β) (hr : ∀ i ∈ J, 0 ≤ r i) (hf : ∀ i ∈ J, Integrable (f i)) :
    Integrable (fun p : Space × Space => β p.2 + ∑ i ∈ J, ∑ z ∈ s,
      selectedCorrection (cube R) a (c i + latticeShift L z + p.1) (r i)
        (fun y => f i (y - c i - latticeShift L z - p.1)) p.2) (μ.prod volume) :=
  (hβ.comp_snd μ).add (integrable_joint_selected_sum μ ha J s c r f hr hf)

/-- The actual core-plus-fluid expression is jointly integrable. Negative
sharp-background terms cause no difficulty because integrability is absolute. -/
theorem integrable_joint_core_fluid {ι : Type*} {L R a : ℝ} (ha : 0 ≤ a)
    (J : Finset ι) (s : Finset LatticeIndex) (c : ι → Space) (r : ι → ℝ)
    (β : Space → ℝ) (core sharp collar : ι → Space → ℝ)
    (hβ : Integrable β) (hr : ∀ i ∈ J, 0 ≤ r i)
    (hcore : ∀ i ∈ J, Integrable (core i)) (hsharp : ∀ i ∈ J, Integrable (sharp i))
    (hcollar : ∀ i ∈ J, Integrable (collar i)) :
    Integrable (fun p : Space × Space => β p.2 -
      (∑ i ∈ J, ∑ z ∈ s, selectedCorrection (cube R) a
        (c i + latticeShift L z + p.1) (r i)
        (fun y => sharp i (y - c i - latticeShift L z - p.1)) p.2) +
      (∑ i ∈ J, ∑ z ∈ s, selectedCorrection (cube R) a
        (c i + latticeShift L z + p.1) (r i)
        (fun y => collar i (y - c i - latticeShift L z - p.1)) p.2) +
      (∑ i ∈ J, ∑ z ∈ s, selectedCorrection (cube R) a
        (c i + latticeShift L z + p.1) (r i)
        (fun y => core i (y - c i - latticeShift L z - p.1)) p.2)) (μ.prod volume) :=
  (((hβ.comp_snd μ).sub (integrable_joint_selected_sum μ ha J s c r sharp hr hsharp)).add
    (integrable_joint_selected_sum μ ha J s c r collar hr hcollar)).add
    (integrable_joint_selected_sum μ ha J s c r core hr hcore)

/-- A state-valued construction with this density identity therefore satisfies
the joint-density integrability required by continuum mixture laws. -/
theorem integrable_of_density_identity {ι : Type*} {L R a : ℝ} (ha : 0 ≤ a)
    (J : Finset ι) (s : Finset LatticeIndex) (c : ι → Space) (r : ι → ℝ)
    (β : Space → ℝ) (f : ι → Space → ℝ) (density : Space → Space → ℝ)
    (hβ : Integrable β) (hr : ∀ i ∈ J, 0 ≤ r i) (hf : ∀ i ∈ J, Integrable (f i))
    (hidentity : ∀ᵐ p : Space × Space ∂μ.prod volume,
      density p.1 p.2 = β p.2 + ∑ i ∈ J, ∑ z ∈ s,
        selectedCorrection (cube R) a (c i + latticeShift L z + p.1) (r i)
          (fun y => f i (y - c i - latticeShift L z - p.1)) p.2) :
    Integrable (fun p : Space × Space => density p.1 p.2) (μ.prod volume) :=
  (integrable_joint_density (L := L) (R := R) μ ha J s c r β f hβ hr hf).congr (by
    filter_upwards [hidentity] with p hp
    exact hp.symm)

/-- Version for profiles already centered at the packing center `c`. Only the
lattice shift and common translation act on such a fixed base profile. -/
theorem integrable_joint_selected_centered {L R a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (c : Space) (z : LatticeIndex) {f : Space → ℝ} (hf : Integrable f) :
    Integrable (fun p : Space × Space =>
      selectedCorrection (cube R) a (c + latticeShift L z + p.1) r
        (fun y => f (y - latticeShift L z - p.1)) p.2) (μ.prod volume) :=
  (integrable_joint_translate μ hf (latticeShift L z)).indicator
    ((measurableSet_selectedBall L R a r c z ha hr).preimage measurable_fst)

theorem integrable_joint_centered_density {ι : Type*} {L R a : ℝ} (ha : 0 ≤ a)
    (J : Finset ι) (s : Finset LatticeIndex) (c : ι → Space) (r : ι → ℝ)
    (β : Space → ℝ) (f : ι → Space → ℝ)
    (hβ : Integrable β) (hr : ∀ i ∈ J, 0 ≤ r i) (hf : ∀ i ∈ J, Integrable (f i)) :
    Integrable (fun p : Space × Space => β p.2 + ∑ i ∈ J, ∑ z ∈ s,
      selectedCorrection (cube R) a (c i + latticeShift L z + p.1) (r i)
        (fun y => f i (y - latticeShift L z - p.1)) p.2) (μ.prod volume) :=
  (hβ.comp_snd μ).add (integrable_finsetSum J fun i hi => integrable_finsetSum s fun z _ =>
    integrable_joint_selected_centered μ ha (hr i hi) (c i) z (hf i hi))

/-- This form matches the finite Fock construction with fixed centered base
states, sharp cores and collar charges. -/
theorem integrable_of_centered_density_identity {ι : Type*} {L R a : ℝ} (ha : 0 ≤ a)
    (J : Finset ι) (s : Finset LatticeIndex) (c : ι → Space) (r : ι → ℝ)
    (β : Space → ℝ) (f : ι → Space → ℝ) (density : Space → Space → ℝ)
    (hβ : Integrable β) (hr : ∀ i ∈ J, 0 ≤ r i) (hf : ∀ i ∈ J, Integrable (f i))
    (hidentity : ∀ᵐ p : Space × Space ∂μ.prod volume,
      density p.1 p.2 = β p.2 + ∑ i ∈ J, ∑ z ∈ s,
        selectedCorrection (cube R) a (c i + latticeShift L z + p.1) (r i)
          (fun y => f i (y - latticeShift L z - p.1)) p.2) :
    Integrable (fun p : Space × Space => density p.1 p.2) (μ.prod volume) :=
  (integrable_joint_centered_density (L := L) (R := R) μ ha J s c r β f hβ hr hf).congr (by
    filter_upwards [hidentity] with p hp
    exact hp.symm)

end Jellium.JointDensity
