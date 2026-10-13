import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Periodic translation averages. The only tiling input is mathlib's ordinary
`IsAddFundamentalDomain` predicate. The finite envelope hypothesis says that
all translates outside the envelope vanish throughout the averaging cell,
as happens for compactly supported functions and a discrete lattice. -/

open Set MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Jellium.Periodic

noncomputable def normalizedRestriction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Q : Set X) : Measure X :=
  (μ Q)⁻¹ • μ.restrict Q

theorem normalizedRestriction_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Q : Set X) (hzero : μ Q ≠ 0) (hfinite : μ Q ≠ ⊤) :
    IsProbabilityMeasure (normalizedRestriction μ Q) := by
  constructor
  simp only [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hzero hfinite

variable {G X : Type*} [AddGroup G] [Countable G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]
  {μ : Measure X} [VAddInvariantMeasure G X μ]

/-- Unfold a finite envelope containing every active periodic translate. The
integrability of each translated piece is deduced from measure preservation. -/
theorem integral_finite_periodization
    {Q : Set X} (hQ : IsAddFundamentalDomain G Q μ) (hQmeas : MeasurableSet Q)
    (f : X → ℝ) (hf : Integrable f μ) (s : Finset G)
    (houtside : ∀ g, g ∉ s → ∀ x ∈ Q, f (g +ᵥ x) = 0) :
    (∫ x in Q, ∑ g ∈ s, f (g +ᵥ x) ∂μ) = ∫ x, f x ∂μ := by
  have hpiece (g : G) : Integrable (fun x => f (g +ᵥ x)) (μ.restrict Q) :=
    ((measurePreserving_vadd g μ).integrable_comp_of_integrable hf).integrableOn
  have hzero (g : G) (hg : g ∉ s) : (∫ x in Q, f (g +ᵥ x) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hQmeas] with x hx
    exact houtside g hg x hx
  calc
    _ = ∑ g ∈ s, ∫ x in Q, f (g +ᵥ x) ∂μ :=
      integral_finsetSum s (fun g _ => hpiece g)
    _ = ∑' g : G, ∫ x in Q, f (g +ᵥ x) ∂μ :=
      (tsum_eq_sum hzero).symm
    _ = ∫ x, f x ∂μ := (hQ.integral_eq_tsum'' f hf).symm

section AdditiveSpace

variable [AddGroup X] [MeasurableAdd X] [MeasurableNeg X]
  [IsAddLeftInvariant μ] [IsNegInvariant μ]

/-- The change of variables used in the manuscript, including reflection and
the fixed observation point, follows from invariance of the ambient measure. -/
theorem integral_finite_translated_periodization
    {Q : Set X} (hQ : IsAddFundamentalDomain G Q μ) (hQmeas : MeasurableSet Q)
    (f : X → ℝ) (hf : Integrable f μ) (s : Finset G) (offset : X)
    (houtside : ∀ g, g ∉ s → ∀ x ∈ Q, f (offset - (g +ᵥ x)) = 0) :
    (∫ x in Q, ∑ g ∈ s, f (offset - (g +ᵥ x)) ∂μ) = ∫ x, f x ∂μ := by
  rw [integral_finite_periodization hQ hQmeas
    (fun x => f (offset - x)) (hf.comp_sub_left offset) s houtside]
  exact integral_sub_left_eq_self f μ offset

/-- A zero-charge correction has exactly zero periodic translation average. -/
theorem integral_finite_translated_periodization_zero
    {Q : Set X} (hQ : IsAddFundamentalDomain G Q μ) (hQmeas : MeasurableSet Q)
    (f : X → ℝ) (hf : Integrable f μ) (s : Finset G) (offset : X)
    (houtside : ∀ g, g ∉ s → ∀ x ∈ Q, f (offset - (g +ᵥ x)) = 0)
    (hcharge : (∫ x, f x ∂μ) = 0) :
    (∫ x in Q, ∑ g ∈ s, f (offset - (g +ᵥ x)) ∂μ) = 0 := by
  rw [integral_finite_translated_periodization hQ hQmeas f hf s offset houtside,
    hcharge]

theorem normalized_finite_translated_periodization
    {Q : Set X} (hQ : IsAddFundamentalDomain G Q μ) (hQmeas : MeasurableSet Q)
    (f : X → ℝ) (hf : Integrable f μ) (s : Finset G) (offset : X)
    (houtside : ∀ g, g ∉ s → ∀ x ∈ Q, f (offset - (g +ᵥ x)) = 0) :
    (∫ x, ∑ g ∈ s, f (offset - (g +ᵥ x)) ∂normalizedRestriction μ Q) =
      (μ Q).toReal⁻¹ * ∫ x, f x ∂μ := by
  rw [normalizedRestriction, integral_smul_measure,
    integral_finite_translated_periodization hQ hQmeas f hf s offset houtside]
  simp only [ENNReal.toReal_inv, smul_eq_mul]

omit [MeasurableNeg X] [IsNegInvariant μ] in
theorem normalized_finite_shifted_periodization
    {Q : Set X} (hQ : IsAddFundamentalDomain G Q μ) (hQmeas : MeasurableSet Q)
    (f : X → ℝ) (hf : Integrable f μ) (s : Finset G) (offset : X)
    (houtside : ∀ g, g ∉ s → ∀ x ∈ Q, f (offset + (g +ᵥ x)) = 0) :
    (∫ x, ∑ g ∈ s, f (offset + (g +ᵥ x)) ∂normalizedRestriction μ Q) =
      (μ Q).toReal⁻¹ * ∫ x, f x ∂μ := by
  rw [normalizedRestriction, integral_smul_measure,
    integral_finite_periodization hQ hQmeas
      (fun x => f (offset + x)) (hf.comp_add_left offset) s houtside,
    integral_add_left_eq_self f offset]
  simp only [ENNReal.toReal_inv, smul_eq_mul]

omit [MeasurableNeg X] [IsNegInvariant μ] in
/-- Exact averaged number of selected translates of a measurable finite-volume
selection region. This replaces any uniform lattice-counting estimate. -/
theorem normalized_selected_count
    {Q A : Set X} (hQ : IsAddFundamentalDomain G Q μ) (hQmeas : MeasurableSet Q)
    (hA : MeasurableSet A) (hAfin : μ A ≠ ⊤)
    (s : Finset G) (offset : X)
    (houtside : ∀ g, g ∉ s → ∀ x ∈ Q, offset + (g +ᵥ x) ∉ A) :
    (∫ x, ∑ g ∈ s, A.indicator (fun _ => (1 : ℝ)) (offset + (g +ᵥ x))
      ∂normalizedRestriction μ Q) = (μ A).toReal / (μ Q).toReal := by
  have hf : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrableOn_const hAfin).integrable_indicator hA
  rw [normalized_finite_shifted_periodization hQ hQmeas _ hf s offset]
  · have hcount : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ) = (μ A).toReal := by
      simpa only [Measure.real, Pi.one_def] using (integral_indicator_one (μ := μ) hA)
    rw [hcount]
    simp only [div_eq_mul_inv, mul_comm]
  · intro g hg x hx
    simp [houtside g hg x hx]

end AdditiveSpace

end Jellium.Periodic
