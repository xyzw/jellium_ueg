import Jellium.OrbitalGeometry
import Jellium.OrbitalAnnulus
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.Integral

/-! The integrable inverse-square penalty in three dimensions. -/

open Set Metric MeasureTheory
open scoped BigOperators

namespace Jellium.OrbitalKernel

open Domains

noncomputable def radialProfile (r : ℝ) : ℝ := if r ≤ 1 then r⁻¹ ^ 2 else 0

noncomputable def kernel (x : Space) : ℝ := 8 * Real.pi ^ 2 * radialProfile ‖x‖

theorem radial_weight (r : ℝ) (hr : 0 < r) :
    r ^ 2 * radialProfile r = (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) r := by
  by_cases h : r ≤ 1
  · simp only [radialProfile, ite_eq_left h, Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, h⟩)]
    field_simp
  · simp [radialProfile, h]

theorem radial_integrable : Integrable (fun x : Space => radialProfile ‖x‖) := by
  rw [integrable_fun_norm_addHaar volume]
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hi : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
    hconst.integrable_indicator measurableSet_Ioc
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  simpa only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
    using (radial_weight r hr).symm

theorem radial_integral : (∫ x : Space, radialProfile ‖x‖) = 4 * Real.pi := by
  rw [integral_fun_norm_addHaar volume]
  have he : (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ Space - 1) • radialProfile r) = 1 := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        simpa only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
          using radial_weight r hr
      _ = ∫ r in Ioc (0 : ℝ) 1, (1 : ℝ) := by
        rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
        rw [Set.inter_eq_left.mpr (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hx => hx.1)]
      _ = 1 := by simp [Real.volume_real_Ioc]
  rw [he, Domains.ball_volume_real (0 : Space) 1 (by norm_num)]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul,
    Domains.ballVolume]
  ring

theorem kernel_nonneg (x : Space) : 0 ≤ kernel x := by
  unfold kernel radialProfile
  split <;> positivity

theorem kernel_integrable : Integrable kernel := radial_integrable.const_mul _

theorem kernel_integral : (∫ x : Space, kernel x) = 32 * Real.pi ^ 3 := by
  unfold kernel
  rw [integral_const_mul, radial_integral]
  ring

theorem kernel_l1 : (∫ x : Space, ‖kernel x‖) = 32 * Real.pi ^ 3 := by
  simp_rw [Real.norm_of_nonneg (kernel_nonneg _)]
  exact kernel_integral

theorem measurable_kernel : Measurable kernel := by
  unfold kernel radialProfile
  apply Measurable.const_mul
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
    (measurable_norm.inv.pow_const 2) measurable_const

noncomputable def w (x y : Space) : ℝ := kernel (x - y)

theorem w_nonneg (x y : Space) : 0 ≤ w x y := kernel_nonneg _

theorem w_eq_shortPair {P : ℕ} (c : Fin P → Space) (i j : Fin P) :
    w (c i) (c j) = 8 * Real.pi ^ 2 * OrbitalGeometry.shortPair c i j := by
  simp only [w, kernel, radialProfile, OrbitalGeometry.shortPair, dist_eq_norm]

theorem pairPenalty_eq_pairSum {P : ℕ} (c : Fin P → Space) :
    OrbitalGeometry.pairPenalty c = OrbitalSampling.pairSum w c := by
  classical
  unfold OrbitalSampling.pairSum OrbitalGeometry.pairPenalty
  simp_rw [w_eq_shortPair, ← Finset.mul_sum]
  ring

theorem measurable_uncurry_w : Measurable (Function.uncurry w) :=
  measurable_kernel.comp (measurable_fst.sub measurable_snd)

theorem integrable_w (x : Space) : Integrable (w x) := kernel_integrable.comp_sub_left x

theorem integral_w (x : Space) : (∫ y, w x y) = 32 * Real.pi ^ 3 := by
  unfold w
  rw [integral_sub_left_eq_self kernel volume x, kernel_integral]

theorem integrable_w_centerLaw {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) (x : Space) :
    Integrable (w x) (OrbitalAnnulus.centerLaw R S) :=
  OrbitalAnnulus.integrable_centerLaw hR hS (integrable_w x).integrableOn

theorem integral_w_centerLaw_le {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) (x : Space) :
    (∫ y, w x y ∂OrbitalAnnulus.centerLaw R S) ≤
      32 * Real.pi ^ 3 / OrbitalAnnulus.centerVolume R S := by
  rw [OrbitalAnnulus.integral_centerLaw hR hS]
  have h := setIntegral_le_integral (s := OrbitalAnnulus.centerRegion R S)
    (integrable_w x) (Filter.Eventually.of_forall (w_nonneg x))
  rw [integral_w] at h
  calc
    _ ≤ (OrbitalAnnulus.centerVolume R S)⁻¹ * (32 * Real.pi ^ 3) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (OrbitalAnnulus.centerVolume_pos hR hS).le)
    _ = _ := by ring

theorem integrable_uncurry_w {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) :
    Integrable (Function.uncurry w)
      ((OrbitalAnnulus.centerLaw R S).prod (OrbitalAnnulus.centerLaw R S)) := by
  let := OrbitalAnnulus.centerLaw_probability hR hS
  apply (integrable_prod_iff measurable_uncurry_w.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (integrable_w_centerLaw hR hS), ?_⟩
  apply Integrable.mono' (integrable_const (32 * Real.pi ^ 3 / OrbitalAnnulus.centerVolume R S))
    measurable_uncurry_w.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg (w_nonneg _ _)]
  rw [Real.norm_of_nonneg (integral_nonneg (w_nonneg x))]
  exact integral_w_centerLaw_le hR hS x

theorem integral_w_centerLaw_prod_le {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) :
    (∫ x, ∫ y, w x y ∂OrbitalAnnulus.centerLaw R S ∂OrbitalAnnulus.centerLaw R S) ≤
      32 * Real.pi ^ 3 / OrbitalAnnulus.centerVolume R S := by
  let := OrbitalAnnulus.centerLaw_probability hR hS
  calc
    _ ≤ ∫ _x : Space, (32 * Real.pi ^ 3 / OrbitalAnnulus.centerVolume R S)
        ∂OrbitalAnnulus.centerLaw R S :=
      integral_mono (integrable_uncurry_w hR hS).integral_prod_left (integrable_const _)
        (integral_w_centerLaw_le hR hS)
    _ = _ := by simp

theorem coulomb_le_kernel (x y : Space) :
    1 / dist x y ≤ 1 + w x y / (8 * Real.pi ^ 2) := by
  have hcoef : 8 * Real.pi ^ 2 ≠ 0 := by positivity
  by_cases hd : dist x y ≤ 1
  · have hw : w x y / (8 * Real.pi ^ 2) = (dist x y)⁻¹ ^ 2 := by
      unfold w kernel radialProfile
      rw [← dist_eq_norm, ite_eq_left hd]
      field_simp
    rw [hw, one_div]
    nlinarith [sq_nonneg ((dist x y)⁻¹ - 1 / 2)]
  · have hdpos : 0 < dist x y := lt_trans zero_lt_one (lt_of_not_ge hd)
    have hle : 1 / dist x y ≤ 1 := (div_le_one hdpos).2 (le_of_not_ge hd)
    have hw : w x y = 0 := by simp [w, kernel, radialProfile, ← dist_eq_norm, hd]
    simpa only [hw, zero_div, add_zero] using hle

theorem integrable_coulomb_centerLaw_prod {R S : ℝ} (hR : 0 < R) (hS : R + 3 ≤ S) :
    Integrable (fun z : Space × Space => 1 / dist z.1 z.2)
      ((OrbitalAnnulus.centerLaw R S).prod (OrbitalAnnulus.centerLaw R S)) := by
  let := OrbitalAnnulus.centerLaw_probability hR hS
  apply Integrable.mono'
    ((integrable_const (1 : ℝ)).add ((integrable_uncurry_w hR hS).div_const (8 * Real.pi ^ 2)))
  · exact (measurable_const.div (measurable_fst.dist measurable_snd)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (one_div_nonneg.mpr dist_nonneg)]
    exact coulomb_le_kernel z.1 z.2

end Jellium.OrbitalKernel
