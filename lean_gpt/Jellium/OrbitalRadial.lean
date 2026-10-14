import Jellium.RadialShells
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
The explicit radial Dirichlet orbital used around each classical particle.
Its reduced radial profile has unit squared integral and Dirichlet integral
`pi^2 / r^2`. The Newton potential of its radial mass equals the point-charge
potential outside its support, and its background loss is bounded directly.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Jellium.OrbitalRadial

/-- The reduced radial profile, so the three-dimensional orbital away from
the centre is `reduced r s / (sqrt (4*pi) * s)`. -/
noncomputable def reduced (r s : ℝ) : ℝ :=
  Real.sqrt (2 / r) * Real.sin ((Real.pi / r) * s)

theorem reduced_contDiff (r : ℝ) : ContDiff ℝ ∞ (reduced r) := by
  exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

theorem reduced_zero (r : ℝ) : reduced r 0 = 0 := by
  simp [reduced]

theorem reduced_endpoint {r : ℝ} (hr : 0 < r) : reduced r r = 0 := by
  simp [reduced, hr.ne']

theorem reduced_hasDerivAt (r s : ℝ) :
    HasDerivAt (reduced r)
      (Real.sqrt (2 / r) * ((Real.pi / r) * Real.cos ((Real.pi / r) * s))) s := by
  change HasDerivAt (fun y => Real.sqrt (2 / r) * Real.sin ((Real.pi / r) * y)) _ s
  simpa only [id_eq, mul_one, mul_assoc, mul_left_comm, mul_comm] using
    (((hasDerivAt_id s).const_mul (Real.pi / r)).sin.const_mul (Real.sqrt (2 / r)))

theorem reduced_deriv (r s : ℝ) :
    deriv (reduced r) s =
      Real.sqrt (2 / r) * ((Real.pi / r) * Real.cos ((Real.pi / r) * s)) :=
  (reduced_hasDerivAt r s).deriv

theorem scaled_sin_sq_integral {r : ℝ} (hr : 0 < r) :
    ∫ s in Icc (0 : ℝ) r, Real.sin ((Real.pi / r) * s) ^ 2 = r / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le,
    intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2)
      (div_ne_zero Real.pi_ne_zero hr.ne'), integral_sin_sq]
  simp only [mul_zero, div_mul_cancel₀ _ hr.ne', Real.sin_zero, zero_mul,
    Real.sin_pi, sub_zero, zero_add, smul_eq_mul, inv_div]
  field_simp

theorem scaled_cos_sq_integral {r : ℝ} (hr : 0 < r) :
    ∫ s in Icc (0 : ℝ) r, Real.cos ((Real.pi / r) * s) ^ 2 = r / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le,
    intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x ^ 2)
      (div_ne_zero Real.pi_ne_zero hr.ne'), integral_cos_sq]
  simp only [mul_zero, div_mul_cancel₀ _ hr.ne', Real.sin_zero, mul_zero,
    Real.sin_pi, sub_zero, zero_add, smul_eq_mul, inv_div]
  field_simp

theorem reduced_normalized {r : ℝ} (hr : 0 < r) :
    ∫ s in Icc (0 : ℝ) r, reduced r s ^ 2 = 1 := by
  simp_rw [reduced, mul_pow, Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le)]
  rw [integral_const_mul, scaled_sin_sq_integral hr]
  field_simp

theorem reduced_kinetic {r : ℝ} (hr : 0 < r) :
    ∫ s in Icc (0 : ℝ) r, deriv (reduced r) s ^ 2 = Real.pi ^ 2 / r ^ 2 := by
  simp_rw [reduced_deriv, mul_pow,
    Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le)]
  rw [integral_const_mul, integral_const_mul, scaled_cos_sq_integral hr]
  field_simp

/-- The one-dimensional radial mass, including the polar Jacobian. -/
noncomputable def mass (r : ℝ) : ℝ → ℝ :=
  (Icc 0 r).indicator (fun s => reduced r s ^ 2)

theorem mass_nonnegative (r s : ℝ) : 0 ≤ mass r s := by
  exact indicator_nonneg (fun s _ => sq_nonneg (reduced r s)) _

theorem mass_integrable (r : ℝ) : Integrable (mass r) := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact ((reduced_contDiff r).continuous.pow 2).integrableOn_Icc

theorem mass_measurable (r : ℝ) : Measurable (mass r) :=
  ((reduced_contDiff r).continuous.pow 2).measurable.indicator measurableSet_Icc

theorem mass_normalized {r : ℝ} (hr : 0 < r) : ∫ s, mass r s = 1 := by
  rw [mass, integral_indicator measurableSet_Icc, reduced_normalized hr]

theorem mass_support (r s : ℝ) (hs : s ∉ Icc 0 r) : mass r s = 0 := by
  simp [mass, hs]

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The zero-extended radial orbital. The value at the centre is irrelevant
to the associated Sobolev and L² classes and is chosen to be zero. -/
noncomputable def orbital (c : Space) (r : ℝ) (x : Space) : ℝ :=
  if dist x c ≤ r then reduced r (dist x c) / (Real.sqrt (4 * Real.pi) * dist x c)
  else 0

noncomputable def density (c : Space) (r : ℝ) (x : Space) : ℝ := orbital c r x ^ 2

theorem orbital_zero_outside (c x : Space) (r : ℝ) (hx : r < dist x c) :
    orbital c r x = 0 := by
  simp [orbital, not_le_of_gt hx]

theorem orbital_zero_boundary (c x : Space) {r : ℝ} (hr : 0 < r)
    (hx : dist x c = r) : orbital c r x = 0 := by
  simp [orbital, hx, reduced_endpoint hr]

theorem orbital_zero_of_radius_le (c x : Space) {r : ℝ} (hr : 0 < r)
    (hx : r ≤ dist x c) : orbital c r x = 0 := by
  rcases eq_or_lt_of_le hx with hx | hx
  · exact orbital_zero_boundary c x hr hx.symm
  · exact orbital_zero_outside c x r hx

theorem density_nonnegative (c : Space) (r : ℝ) (x : Space) : 0 ≤ density c r x :=
  sq_nonneg _

theorem density_zero_outside (c x : Space) (r : ℝ) (hx : r < dist x c) :
    density c r x = 0 := by
  simp [density, orbital_zero_outside c x r hx]

theorem density_radial_mass (c x : Space) (r : ℝ) :
    4 * Real.pi * dist x c ^ 2 * density c r x = mass r (dist x c) := by
  by_cases hx : dist x c ≤ r
  · by_cases hc : dist x c = 0
    · have hr0 : 0 ≤ r := by simpa only [hc] using hx
      simp [density, orbital, mass, hc, hr0, reduced_zero]
    · simp only [density, orbital, hx, ite_true, mass,
        indicator_of_mem (show dist x c ∈ Icc 0 r from ⟨dist_nonneg, hx⟩), div_pow,
        mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 4 * Real.pi)]
      field_simp
  · simp [density, orbital, mass, hx]

/-- Newton's radial kernel is positive for a nonnegative radial mass. -/
theorem potential_nonnegative (μ : ℝ → ℝ) (hμ : ∀ s, 0 ≤ μ s)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ RadialShells.potential μ t := by
  apply integral_nonneg
  intro s
  exact mul_nonneg (hμ s) (one_div_nonneg.mpr (le_trans ht (le_max_left _ _)))

theorem potential_measurable (μ : ℝ → ℝ) (hμ : Measurable μ) :
    Measurable (RadialShells.potential μ) := by
  have hm : Measurable (fun p : ℝ × ℝ => μ p.2 * (1 / max p.1 p.2)) :=
    (hμ.comp measurable_snd).mul (measurable_const.div
      (measurable_fst.max measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem potential_integrable (μ : ℝ → ℝ) (hμ : Integrable μ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun s => μ s * (1 / max t s)) := by
  apply (hμ.abs.const_mul (1 / t)).mono'
  · apply hμ.aestronglyMeasurable.mul
    exact (measurable_const.div (measurable_const.max measurable_id)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro s
    have hden : 0 < max t s := lt_of_lt_of_le ht (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (one_div_nonneg.mpr hden.le)]
    nlinarith [mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le ht (le_max_left t s)) (abs_nonneg (μ s))]

/-- Smearing a positive unit mass cannot exceed the point-charge potential. -/
theorem potential_le_point (μ : ℝ → ℝ) (hμ : Integrable μ)
    (hpos : ∀ s, 0 ≤ μ s) (hmass : ∫ s, μ s = 1)
    {t : ℝ} (ht : 0 < t) : RadialShells.potential μ t ≤ 1 / t := by
  calc
    _ ≤ ∫ s, μ s * (1 / t) := by
      apply integral_mono (potential_integrable μ hμ ht) (hμ.mul_const _)
      intro s
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le ht (le_max_left t s)) (hpos s)
    _ = 1 / t := by rw [integral_mul_const, hmass, one_mul]

theorem potential_eq_point_outside (μ : ℝ → ℝ) {r t : ℝ}
    (hsupport : ∀ s, s ∉ Icc 0 r → μ s = 0)
    (hmass : ∫ s, μ s = 1) (ht : r ≤ t) :
    RadialShells.potential μ t = 1 / t := by
  have heq : (fun s => μ s * (1 / max t s)) = fun s => μ s * (1 / t) := by
    funext s
    by_cases hs : s ∈ Icc 0 r
    · rw [max_eq_left (le_trans hs.2 ht)]
    · simp [hsupport s hs]
  rw [RadialShells.potential, heq, integral_mul_const, hmass, one_mul]

/-- The radial integrand of the point-charge minus smeared potential. -/
noncomputable def defect (μ : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ 2 * (1 / t - RadialShells.potential μ t)

theorem defect_bounds (μ : ℝ → ℝ) (hμ : Integrable μ)
    (hpos : ∀ s, 0 ≤ μ s) (hmass : ∫ s, μ s = 1)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ defect μ t ∧ defect μ t ≤ t := by
  rcases eq_or_lt_of_le ht with ht | ht
  · simp [← ht, defect]
  · have hlo := potential_nonnegative μ hpos ht.le
    have hhi := potential_le_point μ hμ hpos hmass ht
    have hid : t ^ 2 * (1 / t) = t := by field_simp
    constructor
    · exact mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hhi)
    · unfold defect
      nlinarith [mul_nonneg (sq_nonneg t) hlo]

theorem defect_measurable (μ : ℝ → ℝ) (hμ : Measurable μ) :
    Measurable (defect μ) :=
  (measurable_id.pow_const 2).mul
    ((measurable_const.div measurable_id).sub (potential_measurable μ hμ))

theorem defect_integrableOn (μ : ℝ → ℝ) (hμ : Integrable μ)
    (hμmeas : Measurable μ) (hpos : ∀ s, 0 ≤ μ s)
    (hmass : ∫ s, μ s = 1) (r : ℝ) : IntegrableOn (defect μ) (Icc 0 r) := by
  apply continuous_id.integrableOn_Icc.mono' (defect_measurable μ hμmeas).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hd := defect_bounds μ hμ hpos hmass ht.1
  simpa only [Real.norm_eq_abs, abs_of_nonneg hd.1, id_eq] using hd.2

/-- A uniform background of density `rho` loses at most the Coulomb integral
over the ball, giving `2*pi*rho*r^2` for every normalized positive radial mass. -/
noncomputable def backgroundLoss (μ : ℝ → ℝ) (r ρ : ℝ) : ℝ :=
  4 * Real.pi * ρ * ∫ t in Icc (0 : ℝ) r, defect μ t

theorem backgroundLoss_bound (μ : ℝ → ℝ) (hμ : Integrable μ)
    (hpos : ∀ s, 0 ≤ μ s) (hmass : ∫ s, μ s = 1)
    {r ρ : ℝ} (hr : 0 ≤ r) (hρ : 0 ≤ ρ) :
    backgroundLoss μ r ρ ≤ 2 * Real.pi * ρ * r ^ 2 := by
  have hi : (∫ t in Icc (0 : ℝ) r, defect μ t) ≤
      ∫ t in Icc (0 : ℝ) r, t := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact (defect_bounds μ hμ hpos hmass ht.1).1
    · exact continuous_id.integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact (defect_bounds μ hμ hpos hmass ht.1).2
  have hid : (∫ t in Icc (0 : ℝ) r, t) = r ^ 2 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr, integral_id]
    simp
  rw [hid] at hi
  unfold backgroundLoss
  nlinarith [mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ 4 * Real.pi * ρ)]

theorem orbital_backgroundLoss_bound {r ρ : ℝ} (hr : 0 < r)
    (hrhalf : r ≤ 1 / 2) (hρ : 0 ≤ ρ) :
    backgroundLoss (mass r) r ρ ≤ Real.pi / 2 * ρ := by
  have hb := backgroundLoss_bound (mass r) (mass_integrable r)
    (mass_nonnegative r) (mass_normalized hr) hr.le hρ
  have hrsq : r ^ 2 ≤ 1 / 4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hrsq
    (by positivity : 0 ≤ 2 * Real.pi * ρ)
  nlinarith

theorem orbital_potential_eq_point {r t : ℝ} (hr : 0 < r) (ht : r ≤ t) :
    RadialShells.potential (mass r) t = 1 / t :=
  potential_eq_point_outside (mass r) (mass_support r) (mass_normalized hr) ht

/-- The angular fraction of a bounded background contributes a weight between
zero and one to the same radial Coulomb defect. -/
noncomputable def weightedBackgroundLoss (μ : ℝ → ℝ) (r ρ : ℝ)
    (weight : ℝ → ℝ) : ℝ :=
  4 * Real.pi * ρ * ∫ t in Icc (0 : ℝ) r, weight t * defect μ t

theorem weightedDefect_integrableOn (μ : ℝ → ℝ) (hμ : Integrable μ)
    (hμmeas : Measurable μ) (hpos : ∀ s, 0 ≤ μ s)
    (hmass : ∫ s, μ s = 1) (r : ℝ) (weight : ℝ → ℝ)
    (hwmeas : Measurable weight)
    (hweight : ∀ t ∈ Icc 0 r, 0 ≤ weight t ∧ weight t ≤ 1) :
    IntegrableOn (fun t => weight t * defect μ t) (Icc 0 r) := by
  apply continuous_id.integrableOn_Icc.mono'
    (hwmeas.mul (defect_measurable μ hμmeas)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hd := defect_bounds μ hμ hpos hmass ht.1
  have hw := hweight t ht
  change ‖weight t * defect μ t‖ ≤ t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw.1 hd.1)]
  calc
    weight t * defect μ t ≤ 1 * defect μ t := mul_le_mul_of_nonneg_right hw.2 hd.1
    _ ≤ t := by simpa using hd.2

theorem weightedBackgroundLoss_bound (μ : ℝ → ℝ) (hμ : Integrable μ)
    (hpos : ∀ s, 0 ≤ μ s) (hmass : ∫ s, μ s = 1)
    {r ρ : ℝ} (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (weight : ℝ → ℝ)
    (hweight : ∀ t ∈ Icc 0 r, 0 ≤ weight t ∧ weight t ≤ 1) :
    weightedBackgroundLoss μ r ρ weight ≤ 2 * Real.pi * ρ * r ^ 2 := by
  have hi : (∫ t in Icc (0 : ℝ) r, weight t * defect μ t) ≤
      ∫ t in Icc (0 : ℝ) r, t := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_nonneg (hweight t ht).1 (defect_bounds μ hμ hpos hmass ht.1).1
    · exact continuous_id.integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hd := defect_bounds μ hμ hpos hmass ht.1
      calc
        weight t * defect μ t ≤ 1 * defect μ t :=
          mul_le_mul_of_nonneg_right (hweight t ht).2 hd.1
        _ ≤ t := by simpa using hd.2
  have hid : (∫ t in Icc (0 : ℝ) r, t) = r ^ 2 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr, integral_id]
    simp
  rw [hid] at hi
  unfold weightedBackgroundLoss
  nlinarith [mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ 4 * Real.pi * ρ)]

theorem orbital_weightedBackgroundLoss_bound {r ρ : ℝ} (hr : 0 < r)
    (hrhalf : r ≤ 1 / 2) (hρ : 0 ≤ ρ) (weight : ℝ → ℝ)
    (hweight : ∀ t ∈ Icc 0 r, 0 ≤ weight t ∧ weight t ≤ 1) :
    weightedBackgroundLoss (mass r) r ρ weight ≤ Real.pi / 2 * ρ := by
  have hb := weightedBackgroundLoss_bound (mass r) (mass_integrable r)
    (mass_nonnegative r) (mass_normalized hr) hr.le hρ weight hweight
  have hrsq : r ^ 2 ≤ 1 / 4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hrsq
    (by positivity : 0 ≤ 2 * Real.pi * ρ)
  nlinarith

end Jellium.OrbitalRadial
