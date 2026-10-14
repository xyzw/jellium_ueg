import Jellium.OrbitalGeometry
import Jellium.OrbitalRadial
import Jellium.OrbitalSampling

/-!
The local shell state is constructed from the explicit nearest-neighbour
balls and normalized sine profiles. The remaining inputs are general radial
Sobolev/Fock product, Newton and potential-pairing identities for arbitrary
normalized radial profiles. No finite-configuration energy estimate is an
input to the construction.
-/

open MeasureTheory Set Metric
open scoped BigOperators ContDiff

namespace Jellium.OrbitalConstruction

open Domains

/-- A smooth reduced radial profile with zero boundary values and unit mass.
The radial Sobolev isometry sends it to a normalized Dirichlet orbital. -/
structure Profile (r : ℝ) where
  value : ℝ → ℝ
  smooth : ContDiff ℝ ∞ value
  zero : value 0 = 0
  endpoint : value r = 0
  normalized : (∫ s in Icc (0 : ℝ) r, value s ^ 2) = 1

noncomputable def Profile.mass {r : ℝ} (u : Profile r) : ℝ → ℝ :=
  (Icc 0 r).indicator (fun s => u.value s ^ 2)

theorem Profile.mass_normalized {r : ℝ} (u : Profile r) : ∫ s, u.mass s = 1 := by
  rw [Profile.mass, integral_indicator measurableSet_Icc, u.normalized]

noncomputable def Profile.density {r : ℝ} (u : Profile r) (c x : Space) : ℝ :=
  if dist x c ≤ r then
    (u.value (dist x c) / (Real.sqrt (4 * Real.pi) * dist x c)) ^ 2
  else 0

noncomputable def Profile.kinetic {r : ℝ} (u : Profile r) : ℝ :=
  ∫ s in Icc (0 : ℝ) r, deriv u.value s ^ 2

noncomputable def sineProfile {r : ℝ} (hr : 0 < r) : Profile r where
  value := OrbitalRadial.reduced r
  smooth := OrbitalRadial.reduced_contDiff r
  zero := OrbitalRadial.reduced_zero r
  endpoint := OrbitalRadial.reduced_endpoint hr
  normalized := OrbitalRadial.reduced_normalized hr

theorem sineProfile_mass {r : ℝ} (hr : 0 < r) :
    (sineProfile hr).mass = OrbitalRadial.mass r := rfl

theorem sineProfile_kinetic {r : ℝ} (hr : 0 < r) :
    (sineProfile hr).kinetic = (Real.pi / r) ^ 2 := by
  rw [Profile.kinetic, sineProfile, OrbitalRadial.reduced_kinetic hr, div_pow]

noncomputable def average {r : ℝ} (u : Profile r) (c : Space) (v : Space → ℝ) : ℝ :=
  ∫ x, u.density c x * v x

noncomputable def coulomb (f g : Space → ℝ) : ℝ :=
  ∫ x, ∫ y, f x * g y / dist x y

noncomputable def pointKernel (x y : Space) : ℝ := 1 / dist x y

/-- General operator and electrostatic identities. The product rule applies
to arbitrary normalized smooth reduced profiles, rather than the chosen sine
orbitals. Newton and the harmonic mean-value property are likewise stated
for arbitrary profiles. The background formula is the exact polar/Fubini
identity with an angular occupation fraction between zero and one. -/
structure OperatorLaws {State : Type*}
    (energy : ℝ → State → ℝ) (confined : ℝ → ℕ → State → Prop) (ρ : ℝ) where
  kineticCoeff : ℝ
  kineticCoeff_nonnegative : 0 ≤ kineticCoeff
  corePotential : ℝ → State → Space → ℝ
  backgroundPotential : ℝ → ℝ → Space → ℝ
  backgroundConstant : ℝ → ℝ → State → ℝ
  angularWeight : ℝ → ℝ → Space → ℝ → ℝ
  angularWeight_measurable : ∀ R S c, Measurable (angularWeight R S c)
  angularWeight_bounds : ∀ R S c t, 0 ≤ angularWeight R S c t ∧ angularWeight R S c t ≤ 1
  newton_pair : ∀ {r s : ℝ} (u : Profile r) (v : Profile s) (c d : Space),
    0 < r → 0 < s → r + s ≤ dist c d →
    coulomb (u.density c) (v.density d) =
      RadialShells.potential u.mass (dist c d) * ∫ t, v.mass t
  core_mean : ∀ {R r : ℝ} {N : ℕ} {Γ : State} (u : Profile r) (c : Space),
    0 < R → 0 < r → confined R N Γ → R + r < ‖c‖ →
    average u c (corePotential R Γ) = corePotential R Γ c
  background_mean : ∀ {r : ℝ} (u : Profile r) (R S : ℝ) (c : Space),
    0 < r →
    average u c (backgroundPotential R S) = backgroundPotential R S c -
      OrbitalRadial.weightedBackgroundLoss u.mass r ρ (angularWeight R S c)
  product : ∀ {R S : ℝ} {N : ℕ} {Γ : State} {P : ℕ}
      (c : Fin P → Space) (r : Fin P → ℝ) (u : ∀ i, Profile (r i)),
    0 < R → confined R N Γ → (∀ i, 0 < r i) →
    (Pairwise fun i j => Disjoint (ball (c i) (r i)) (ball (c j) (r j))) →
    (∀ i, closedBall (c i) (r i) ⊆ {x : Space | R < ‖x‖ ∧ ‖x‖ < S}) →
    ∃ Ψ, confined S (N + P) Ψ ∧
      energy S Ψ = energy R Γ + kineticCoeff * (∑ i, (u i).kinetic) +
        (∑ i, ∑ j ∈ Finset.univ.erase i,
          coulomb ((u i).density (c i)) ((u j).density (c j))) / 2 +
        (∑ i, (average (u i) (c i) (corePotential R Γ) -
          average (u i) (c i) (backgroundPotential R S))) + backgroundConstant R S Γ

noncomputable def OperatorLaws.oneBody {State : Type*}
    {energy : ℝ → State → ℝ} {confined : ℝ → ℕ → State → Prop} {ρ : ℝ}
    (laws : OperatorLaws energy confined ρ) (R S : ℝ) (Γ : State) (x : Space) : ℝ :=
  laws.corePotential R Γ x - laws.backgroundPotential R S x

/-- The local orbital estimate is a theorem. Its constants are the proved
kinetic cost `4*pi^2` and background cost `pi*rho/2` per particle. -/
theorem exists_local_state {State : Type*}
    {energy : ℝ → State → ℝ} {confined : ℝ → ℕ → State → Prop} {ρ R S : ℝ}
    {N P : ℕ} {Γ : State}
    (laws : OperatorLaws energy confined ρ) (hρ : 0 ≤ ρ) (hR : 0 < R)
    (hΓ : confined R N Γ) (c : Fin P → Space) (hc : Function.Injective c)
    (hcenters : ∀ i, R + 1 < ‖c i‖ ∧ ‖c i‖ < S - 1) :
    ∃ Ψ, confined S (N + P) Ψ ∧
      energy S Ψ ≤ energy R Γ +
        OrbitalSampling.classicalEnergy pointKernel (laws.oneBody R S Γ)
          (laws.backgroundConstant R S Γ) c +
        laws.kineticCoeff * OrbitalGeometry.pairPenalty c +
        (4 * Real.pi ^ 2 * laws.kineticCoeff + Real.pi / 2 * ρ) * P := by
  classical
  let r := OrbitalGeometry.radius c
  have hr (i : Fin P) : 0 < r i := OrbitalGeometry.radius_pos c hc i
  let u (i : Fin P) := sineProfile (hr i)
  obtain ⟨Ψ, hΨ, hE⟩ := laws.product c r u hR hΓ hr
    (OrbitalGeometry.balls_pairwise_disjoint c)
    (fun i => OrbitalGeometry.closedBall_subset_annulus c i R S
      (hcenters i).1 (hcenters i).2)
  have hpair (i j : Fin P) (hij : i ≠ j) :
      coulomb ((u i).density (c i)) ((u j).density (c j)) = pointKernel (c i) (c j) := by
    have hi := OrbitalGeometry.radius_le_half_dist c i j hij
    have hj := OrbitalGeometry.radius_le_half_dist c j i hij.symm
    rw [dist_comm (c j) (c i)] at hj
    have hsep : r i + r j ≤ dist (c i) (c j) := by
      change OrbitalGeometry.radius c i + OrbitalGeometry.radius c j ≤ _
      linarith
    rw [laws.newton_pair (u i) (u j) (c i) (c j) (hr i) (hr j) hsep,
      Profile.mass_normalized, mul_one]
    change RadialShells.potential (OrbitalRadial.mass (r i)) (dist (c i) (c j)) = _
    exact OrbitalRadial.orbital_potential_eq_point (hr i) (by linarith [hr j])
  have hpairSum :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        coulomb ((u i).density (c i)) ((u j).density (c j))) / 2 =
        OrbitalSampling.pairSum pointKernel c := by
    unfold OrbitalSampling.pairSum
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    exact hpair i j (Finset.ne_of_mem_erase hj).symm
  have hkin : (∑ i, (u i).kinetic) = OrbitalGeometry.kineticSum c := by
    apply Finset.sum_congr rfl
    intro i _
    exact sineProfile_kinetic (hr i)
  have hone (i : Fin P) :
      average (u i) (c i) (laws.corePotential R Γ) -
        average (u i) (c i) (laws.backgroundPotential R S) ≤
        laws.oneBody R S Γ (c i) + Real.pi / 2 * ρ := by
    have hsep : R + r i < ‖c i‖ := by
      have hh := OrbitalGeometry.radius_le_half c i
      have hi := (hcenters i).1
      dsimp [r]
      linarith
    rw [laws.core_mean (u i) (c i) hR (hr i) hΓ hsep,
      laws.background_mean (u i) R S (c i) (hr i)]
    have hb := OrbitalRadial.orbital_weightedBackgroundLoss_bound (hr i)
      (OrbitalGeometry.radius_le_half c i) hρ (laws.angularWeight R S (c i))
      (fun t _ => laws.angularWeight_bounds R S (c i) t)
    change _ - (_ - OrbitalRadial.weightedBackgroundLoss
      (OrbitalRadial.mass (r i)) (r i) ρ _) ≤ _
    dsimp [OperatorLaws.oneBody]
    linarith
  have hones := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hone i)
  have hs : (∑ i, (laws.oneBody R S Γ (c i) + Real.pi / 2 * ρ)) =
      OrbitalSampling.oneBodySum (laws.oneBody R S Γ) c + (Real.pi / 2 * ρ) * P := by
    simp [OrbitalSampling.oneBodySum, Finset.sum_add_distrib, mul_comm]
  rw [hs] at hones
  refine ⟨Ψ, hΨ, ?_⟩
  rw [hE, hkin, hpairSum]
  have hk := mul_le_mul_of_nonneg_left (OrbitalGeometry.kinetic_sum_bound c)
    laws.kineticCoeff_nonnegative
  unfold OrbitalSampling.classicalEnergy
  linarith

end Jellium.OrbitalConstruction
