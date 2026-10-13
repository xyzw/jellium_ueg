import Jellium.DomainLayers
import Mathlib.Analysis.SpecificLimits.Basic

/-! LN admissibility of actual lattice-ball domains.

The double-layer potentials below use the classical radial Newton formula.
`DomainLayers` proves that the distance layers are exactly the component
spherical shells and that the global compensation coefficients are the single
component coefficients. Endpoints of radial intervals do not affect these
Lebesgue integrals. Neutrality makes distinct component interactions zero, so
the full Coulomb energies are the sums of the component radial energies.
For each fixed h, the finitely many earlier overlapping distance layers have
finite positive outer-layer volumes and bounded compactly supported densities,
hence finite potentials and Coulomb energies by the ordinary L1/L-infinity
Coulomb estimate. They do not affect the limits or fixed-h bounded ratios.
-/

open Set Metric Filter Topology MeasureTheory
open scoped BigOperators

namespace Jellium.Domains

noncomputable def layerPotential (R h : ℝ) (m : ℕ) (outer : Bool) (x : Space) : ℝ :=
  ∑ i : Grid m, RadialShells.potential
    (if outer then RadialShells.outer R h else RadialShells.inner R h) (dist x (center R i))

noncomputable def layerEnergy (R h : ℝ) (m : ℕ) (outer : Bool) : ℝ :=
  (m : ℝ) ^ 3 * RadialShells.energy
    (if outer then RadialShells.outer R h else RadialShells.inner R h)

theorem layerPotential_bound (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R)
    (m : ℕ) (outer : Bool) (x : Space) :
    |layerPotential R h m outer x| ≤ 256 * Real.pi * h ^ 2 := by
  classical
  have hzero (i : Grid m) (hi : x ∉ closedBall (center R i) (R + 2 * h)) :
      RadialShells.potential
        (if outer then RadialShells.outer R h else RadialShells.inner R h)
        (dist x (center R i)) = 0 := by
    have hd : R + 2 * h < dist x (center R i) := lt_of_not_ge hi
    cases outer
    · exact RadialShells.inner_potential_zero R h _ hh hR (by linarith)
    · exact RadialShells.outer_potential_zero R h _ hh hR hd.le
  unfold layerPotential
  by_cases hx : ∃ i : Grid m, x ∈ closedBall (center R i) (R + 2 * h)
  · obtain ⟨i, hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · cases outer
      · exact RadialShells.inner_potential_bound R h _ hh hR
      · exact RadialShells.outer_potential_bound R h _ hh hR
    · intro j _ hji
      apply hzero
      intro hj
      exact Set.disjoint_left.mp (enlarged_closed_balls_pairwise_disjoint R h hh.le hR m hji) hj hi
    · simp
  · have hz : ∀ i : Grid m, x ∉ closedBall (center R i) (R + 2 * h) := by
      intro i hi
      exact hx ⟨i, hi⟩
    rw [Finset.sum_eq_zero (fun i _ => hzero i (hz i)), abs_zero]
    positivity

theorem layerEnergy_bound (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R)
    (m : ℕ) (outer : Bool) :
    |layerEnergy R h m outer| ≤ (m : ℝ) ^ 3 * (4096 * Real.pi ^ 2 * R ^ 2 * h ^ 3) := by
  unfold layerEnergy
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 3)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  cases outer
  · exact RadialShells.inner_energy_bound R h hh hR
  · exact RadialShells.outer_energy_bound R h hh hR

theorem normalized_layerEnergy_bound (R h : ℝ) (hh : 0 < h) (hR : 4 * h < R)
    (m : ℕ) (hm : 1 ≤ m) (outer : Bool) :
    |layerEnergy R h m outer / volume.real (latticeBalls R m)| ≤
      (3072 * Real.pi * h ^ 3) / R := by
  have hRpos : 0 < R := by linarith
  have hV := latticeBalls_volume_pos R hRpos m hm
  rw [abs_div, abs_of_pos hV]
  apply (div_le_iff₀ hV).2
  calc
    _ ≤ (m : ℝ) ^ 3 * (4096 * Real.pi ^ 2 * R ^ 2 * h ^ 3) :=
      layerEnergy_bound R h hh hR m outer
    _ = _ := by
      rw [latticeBalls_volume R hRpos.le]
      unfold ballVolume
      field_simp
      ring

theorem lattice_layerEnergy_limit (R : ℕ → ℝ) (m : ℕ → ℕ)
    (hm : ∀ j, 1 ≤ m j)
    (hR : Tendsto R atTop atTop) (h : ℝ) (hh : 0 < h) (outer : Bool) :
    Tendsto (fun j => layerEnergy (R j) h (m j) outer /
      volume.real (latticeBalls (R j) (m j))) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ j in atTop, 4 * h < R j := (tendsto_atTop.1 hR) (4 * h + 1) |>.mono
    (fun _ hj => by linarith)
  have hbound : ∀ᶠ j in atTop,
      |layerEnergy (R j) h (m j) outer / volume.real (latticeBalls (R j) (m j))| ≤
        (3072 * Real.pi * h ^ 3) / R j := by
    filter_upwards [hlarge] with j hj
    exact normalized_layerEnergy_bound (R j) h hh hj (m j) (hm j) outer
  have hlim : Tendsto (fun j => (3072 * Real.pi * h ^ 3) / R j) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hR).const_mul (3072 * Real.pi * h ^ 3)
  exact squeeze_zero_norm' hbound hlim

theorem lattice_volume_tendsto (R : ℕ → ℝ) (m : ℕ → ℕ)
    (hRpos : ∀ j, 0 < R j) (hm : ∀ j, 1 ≤ m j)
    (hR : Tendsto R atTop atTop) :
    Tendsto (fun j => volume.real (latticeBalls (R j) (m j))) atTop atTop := by
  have hball : Tendsto (fun j => ballVolume (R j)) atTop atTop :=
    ((tendsto_pow_atTop (by decide : 3 ≠ 0)).comp hR).const_mul_atTop (by positivity)
  apply tendsto_atTop_mono _ hball
  intro j
  rw [latticeBalls_volume (R j) (hRpos j).le]
  have hmcast : (1 : ℝ) ≤ m j := by exact_mod_cast hm j
  have hm3 : (1 : ℝ) ≤ (m j : ℝ) ^ 3 := by nlinarith [sq_nonneg ((m j : ℝ) - 1)]
  have hV : 0 ≤ ballVolume (R j) := by unfold ballVolume; have := hRpos j; positivity
  nlinarith [mul_le_mul_of_nonneg_right hm3 hV]

theorem radius_uniform_positive (R : ℕ → ℝ) (hpos : ∀ j, 0 < R j)
    (hR : Tendsto R atTop atTop) : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ j, r₀ ≤ R j := by
  have hprefix (N : ℕ) : ∃ r : ℝ, 0 < r ∧ ∀ j, j < N → r ≤ R j := by
    induction N with
    | zero => exact ⟨1, zero_lt_one, fun j hj => (Nat.not_lt_zero j hj).elim⟩
    | succ N ih =>
      obtain ⟨r, hr, hb⟩ := ih
      refine ⟨min r (R N), lt_min hr (hpos N), ?_⟩
      intro j hj
      by_cases hlt : j < N
      · exact (min_le_left _ _).trans (hb j hlt)
      · have heq : j = N := by omega
        subst j
        exact min_le_right _ _
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_atTop.1 hR) 1)
  obtain ⟨r, hr, hb⟩ := hprefix N
  refine ⟨min 1 r, lt_min zero_lt_one hr, ?_⟩
  intro j
  by_cases hj : j < N
  · exact (min_le_right _ _).trans (hb j hj)
  · exact (min_le_left _ _).trans (hN j (Nat.le_of_not_gt hj))

/-- Explicit sufficient LN data. Potentials and energies use the exact Newton
radial representation of the actual distance layers, whose sets and volume
ratios were computed in `DomainLayers`. The uniform small-thickness estimate is
recorded uniformly for every index, using a positive lower bound on all radii. -/
structure LatticeLNAdmissible (R : ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  radius_positive : ∀ j, 0 < R j
  radius_infinite : Tendsto R atTop atTop
  multiplicity_positive : ∀ j, 1 ≤ m j
  open_domain : ∀ j, IsOpen (latticeBalls (R j) (m j))
  bounded_domain : ∀ j, Bornology.IsBounded (latticeBalls (R j) (m j))
  volume_infinite : Tendsto (fun j => volume.real (latticeBalls (R j) (m j))) atTop atTop
  vanHove : ∀ h, 0 < h → Tendsto (fun j =>
    volume.real (cthickening h (frontier (latticeBalls (R j) (m j)))) /
      volume.real (latticeBalls (R j) (m j))) atTop (𝓝 0)
  enclosing : ∀ j, latticeBalls (R j) (m j) ⊆ ball 0 (7 * R j * m j) ∧
    volume.real (ball (0 : Space) (7 * R j * m j)) =
      343 * volume.real (latticeBalls (R j) (m j))
  ratio : ∀ h, 0 < h → ∀ᶠ j in atTop,
    volume.real (outerFirstLayer (latticeBalls (R j) (m j)) h) /
      volume.real (outerSecondLayer (latticeBalls (R j) (m j)) h) ≤ 1
  potential : ∀ h, 0 < h → ∀ᶠ j in atTop, ∀ x,
    |layerPotential (R j) h (m j) true x| ≤ 256 * Real.pi * h ^ 2
  small_thickness : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ h, 0 < h → h < r₀ / 4 → ∀ j x,
    |layerPotential (R j) h (m j) true x| ≤ 256 * Real.pi * h ^ 2
  outer_energy : ∀ h, 0 < h → Tendsto (fun j =>
    layerEnergy (R j) h (m j) true / volume.real (latticeBalls (R j) (m j))) atTop (𝓝 0)
  inner_energy : ∀ h, 0 < h → Tendsto (fun j =>
    layerEnergy (R j) h (m j) false / volume.real (latticeBalls (R j) (m j))) atTop (𝓝 0)

theorem lattice_LN_admissible (R : ℕ → ℝ) (m : ℕ → ℕ)
    (hRpos : ∀ j, 0 < R j) (hm : ∀ j, 1 ≤ m j)
    (hR : Tendsto R atTop atTop) : LatticeLNAdmissible R m := by
  refine ⟨hRpos, hR, hm, (fun j => latticeBalls_open _ _), ?_,
    lattice_volume_tendsto R m hRpos hm hR, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact isBounded_ball.subset (latticeBalls_subset_enclosing_ball (R j) (hRpos j) (m j) (hm j))
  · intro h hh
    exact lattice_vanHove R m hRpos hm hR h hh.le
  · intro j
    exact ⟨latticeBalls_subset_enclosing_ball (R j) (hRpos j) (m j) (hm j),
      enclosing_ball_volume (R j) (hRpos j).le (m j)⟩
  · intro h hh
    filter_upwards [(tendsto_atTop.1 hR) (4 * h + 1)] with j hj
    rw [lattice_outer_ratio (R j) h hh (by linarith) (m j) (hm j)]
    exact (RadialShells.outer_ratio_bound (R j) h hh (by linarith)).2
  · intro h hh
    filter_upwards [(tendsto_atTop.1 hR) (4 * h + 1)] with j hj
    exact fun x => layerPotential_bound (R j) h hh (by linarith) (m j) true x
  · obtain ⟨r₀, hr₀, hlow⟩ := radius_uniform_positive R hRpos hR
    refine ⟨r₀, hr₀, ?_⟩
    intro h hh hsmall j x
    have hjR := hlow j
    exact layerPotential_bound (R j) h hh (by linarith) (m j) true x
  · intro h hh
    exact lattice_layerEnergy_limit R m hm hR h hh true
  · intro h hh
    exact lattice_layerEnergy_limit R m hm hR h hh false

/-- The explicit potential control tends to zero with the layer thickness. -/
theorem layerPotential_constant_tendsto :
    Tendsto (fun h : ℝ => 256 * Real.pi * h ^ 2) (𝓝 0) (𝓝 0) := by
  simpa using ((continuous_id.pow 2).const_mul (256 * Real.pi)).tendsto 0

end Jellium.Domains
