import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
The scalar deduction in the bounded transition layer lemma.

The analytical inputs remain explicit hypotheses. They include the smeared
Graf–Schenker localization inequality, the geometric estimate for the total
boundary contribution, and convergence of the smeared tetrahedron energy.
No theorem about a density, a quantum state, or a geometric tiling is postulated
in this file. The scalar asymptotic conclusion is proved here from the explicit
prelimit estimate, rather than introduced as a literature assumption.
-/

open Filter Topology
open scoped BigOperators

namespace Jellium.Localization

/-- A subset of a finite nonnegative partition of unity has power sum at most
one for every exponent at least one. Applied pointwise with `p = 4 / 3`, this
is the scalar step in the Lieb–Oxford boundary estimate. It prevents the
bound from depending on how many localized cells overlap. -/
theorem boundary_partition_rpow_sum_le_one
    {ι : Type*} (tiles boundary : Finset ι) (ξ : ι → ℝ) {p : ℝ}
    (hsubset : boundary ⊆ tiles)
    (hnonneg : ∀ i ∈ tiles, 0 ≤ ξ i)
    (hpartition : ∑ i ∈ tiles, ξ i = 1)
    (hp : 1 ≤ p) :
    ∑ i ∈ boundary, (ξ i) ^ p ≤ 1 := by
  have hle_one (i : ι) (hi : i ∈ tiles) : ξ i ≤ 1 := by
    simpa only [hpartition] using Finset.single_le_sum hnonneg hi
  calc
    ∑ i ∈ boundary, (ξ i) ^ p ≤ ∑ i ∈ boundary, ξ i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_self_of_le_one
        (hnonneg i (hsubset hi)) (hle_one i (hsubset hi)) hp
    _ ≤ ∑ i ∈ tiles, ξ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i hi _ => hnonneg i hi)
    _ = 1 := hpartition

/-- Missing interior volume has a controlled cost regardless of the sign of
the energy of one cell. The geometric cell-count hypotheses are kept explicit.
In the manuscript, `missing` can be chosen as `C * R^2 * H_R`. -/
theorem interior_count_lower_bound
    {count volume cellVolume cellEnergy missing : ℝ}
    (hv : 0 < cellVolume)
    (hinside : count * cellVolume ≤ volume)
    (hmissing : volume - count * cellVolume ≤ missing) :
    volume * (cellEnergy / cellVolume) -
      missing * (|cellEnergy| / cellVolume) ≤ count * cellEnergy := by
  have hsign := mul_nonneg (sub_nonneg.mpr hinside)
    (sub_nonneg.mpr (le_abs_self cellEnergy))
  have hloss := mul_nonneg (sub_nonneg.mpr hmissing) (abs_nonneg cellEnergy)
  apply (le_of_mul_le_mul_right · hv)
  field_simp
  nlinarith

/-- Inserting the local-cell lower bound is legitimate because the
localization prefactor is nonnegative. -/
theorem insert_local_sum_bound
    {energy localSum main boundary remainder κ : ℝ}
    (hκ : 0 ≤ κ)
    (hlocal : κ * localSum - remainder ≤ energy)
    (hsum : main - boundary ≤ localSum) :
    κ * main - κ * boundary - remainder ≤ energy := by
  have := mul_le_mul_of_nonneg_left hsum hκ
  nlinarith

/-- A lower bound with two successively vanishing errors. The outer parameter
is chosen first, and the large-system limit is then taken with that parameter
fixed. This is the precise quantifier order used by the localization proof. -/
theorem two_limit_lower_bound
    {α β : Type*} {f : Filter α} {g : Filter β} [NeBot g]
    {energy : α → ℝ} {main : β → ℝ} {error : β → α → ℝ} {limit : ℝ}
    (hmain : Tendsto main g (𝓝 limit))
    (herror : ∀ᶠ l in g, Tendsto (error l) f (𝓝 0))
    (hbound : ∀ᶠ l in g, ∀ᶠ R in f, main l - error l R ≤ energy R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R in f, limit - ε ≤ energy R := by
  have hhalf : 0 < ε / 2 := by linarith
  have hnear : ∀ᶠ l in g, limit - ε / 2 < main l :=
    (tendsto_order.1 hmain).1 _ (by linarith)
  obtain ⟨l, hlnear, hlerror, hlbound⟩ := (hnear.and (herror.and hbound)).exists
  have herrnear : ∀ᶠ R in f, error l R < ε / 2 :=
    (tendsto_order.1 hlerror).2 _ hhalf
  filter_upwards [herrnear, hlbound] with R hRerr hRbound
  linarith

/-- The prefactor in the localization estimate tends to one. -/
theorem tendsto_localization_factor (C : ℝ) :
    Tendsto (fun l : ℝ => 1 - C / l) atTop (𝓝 1) := by
  have hdiv : Tendsto (fun l : ℝ => C / l) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun l : ℝ => C * l⁻¹) atTop (𝓝 (C * 0)))
  simpa using tendsto_const_nhds.sub hdiv

/-- At a fixed cell scale, enlarging a sublinear transition width by a fixed
amount still gives a negligible fraction of the box side length. The fixed
amount in the manuscript is `d₀ * l + 2 * s + 1`. -/
theorem enlarged_boundary_ratio_tendsto
    {width : ℝ → ℝ}
    (hwidth : Tendsto (fun R => width R / R) atTop (𝓝 (0 : ℝ)))
    (fixedWidth : ℝ) :
    Tendsto (fun R => (width R + fixedWidth) / R) atTop (𝓝 (0 : ℝ)) := by
  have hfixed : Tendsto (fun R : ℝ => fixedWidth / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun R : ℝ => fixedWidth * R⁻¹) atTop (𝓝 (fixedWidth * 0)))
  simpa only [add_div, add_zero] using hwidth.add hfixed

/-- The exact numerical form of the estimate at the end of the bounded
transition layer proof. Here `energy R` is `E_hbar(rho_R) / R^3`, `cell l` is
`F_l / v_l`, and `boundaryRatio l R` is `H_R / R` with `l` fixed. The constants
`A` and `K` absorb the fixed density and spin parameters.

The hypothesis `hbound` is the combination of localization, the interior cell
count, the Lieb–Oxford boundary estimate, and the extensive density bound.
Those analytical and geometric steps are not formalized by this theorem.
There is deliberately no hypothesis bounding the kinetic energy of `rho_R`.
-/
theorem bounded_transition_layer_lower_bound
    {energy cell : ℝ → ℝ} {boundaryRatio : ℝ → ℝ → ℝ}
    {ueg C K A : ℝ}
    (hcell : Tendsto cell atTop (𝓝 ueg))
    (hboundary : ∀ᶠ l in atTop, Tendsto (boundaryRatio l) atTop (𝓝 0))
    (hbound : ∀ᶠ l in atTop, ∀ᶠ R in atTop,
      (1 - C / l) * cell l -
        (1 - C / l) * boundaryRatio l R * (|cell l| + A) - K / l ≤ energy R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R in atTop, ueg - ε ≤ energy R := by
  have hK : Tendsto (fun l : ℝ => K / l) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun l : ℝ => K * l⁻¹) atTop (𝓝 (K * 0)))
  have hmain : Tendsto (fun l : ℝ => (1 - C / l) * cell l - K / l)
      atTop (𝓝 ueg) := by
    simpa using ((tendsto_localization_factor C).mul hcell).sub hK
  have herror : ∀ᶠ l in atTop,
      Tendsto (fun R => (1 - C / l) * boundaryRatio l R * (|cell l| + A))
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hboundary] with l hl
    simpa using (tendsto_const_nhds.mul hl).mul_const (|cell l| + A)
  apply two_limit_lower_bound hmain herror _ ε hε
  filter_upwards [hbound] with l hl
  filter_upwards [hl] with R hR
  linarith

end Jellium.Localization
