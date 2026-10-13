import Jellium.ProbabilityApproximation
import Jellium.CanonicalConstruction
import Jellium.LNAdmissibility
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact canonical replication of arbitrary finite-energy sector laws. -/

open scoped BigOperators
open Filter Topology MeasureTheory

namespace Jellium.Canonicalization

open ProbabilityApproximation CanonicalConstruction Domains

variable {State : Type*}

/-- Standard radial Fock product and mixture operations in every finite lattice
of balls, tied to the physical energy and Dirichlet admissibility on that domain.
The same chosen sector state is used in each ball. -/
structure ReplicableBall (State : Type*) (R : ℝ) (n : ℕ)
    (sectorEnergy : ℕ → ℝ)
    (energy : Set Space → State → ℝ)
    (admissible : Set Space → ℕ → State → Prop) where
  operations : (m : ℕ) → FermionBallOperations (Grid m) State
  reference_eq : ∀ m, (operations m).reference = n
  sectorEnergy_eq : ∀ m, (operations m).sectorEnergy = sectorEnergy
  available : ∀ m k, (operations m).availableSector k
  energy_eq : ∀ m, (operations m).energy = energy (latticeBalls R m)
  canonical_eq : ∀ m, (operations m).canonical = admissible (latticeBalls R m)

/-- The approximation list and exact canonical state are constructed internally.
There is no finite-support, rational-weight, or list hypothesis. -/
theorem exists_canonical_replication
    (R : ℝ) (n : ℕ) (p sectorEnergy : ℕ → ℝ)
    (energy : Set Space → State → ℝ)
    (admissible : Set Space → ℕ → State → Prop)
    (ops : ReplicableBall State R n sectorEnergy energy admissible)
    (hp : ∀ k, 0 ≤ p k) (hpsum : Summable p)
    (hmeanSum : Summable (fun k : ℕ => (k : ℝ) * p k))
    (henergySum : Summable (fun k => p k * sectorEnergy k))
    (hmass : ∑' k, p k = 1) (hmean : ∑' k : ℕ, (k : ℝ) * p k = n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ Γ : State,
      admissible (latticeBalls R m) (m ^ 3 * n) Γ ∧
      energy (latticeBalls R m) Γ / (m ^ 3 : ℕ) ≤
        (∑' k, p k * sectorEnergy k) + ε := by
  classical
  obtain ⟨m, K, hm, count, hcard, hcount, herr⟩ :=
    exists_cubic_sector_list p sectorEnergy n hp hpsum hmeanSum henergySum
      hmass hmean ε hε
  let e : Grid m ≃ RepeatedIndex count := Fintype.equivOfCardEq (by
    rw [grid_card, hcard])
  let sectors : Grid m → ℕ := fun i => (e i).1.val
  have hsectors : ∑ i, sectors i = Fintype.card (Grid m) * (ops.operations m).reference := by
    have heq : (∑ i : Grid m, sectors i) = ∑ j : RepeatedIndex count, j.1.val :=
      Equiv.sum_comp e (fun j : RepeatedIndex count => j.1.val)
    rw [heq, hcount, grid_card, ops.reference_eq]
  have hm3 : 1 < Fintype.card (Grid m) := by
    rw [grid_card]
    nlinarith [Nat.pow_le_pow_left hm 3]
  have hM : (0 : ℝ) < (m ^ 3 : ℕ) := by positivity
  obtain ⟨Γ, hΓ, hE⟩ := exists_neutral_state_energy_le (ops.operations m) sectors
    (fun i => ops.available m (sectors i)) hm3 hsectors
  refine ⟨m, hm, Γ, ?_, ?_⟩
  · simpa only [grid_card, ops.reference_eq, ops.canonical_eq] using hΓ
  · rw [ops.energy_eq, ops.sectorEnergy_eq] at hE
    have hsum : (∑ i : Grid m, sectorEnergy (sectors i)) =
        ∑ j : RepeatedIndex count, sectorEnergy j.1.val :=
      Equiv.sum_comp e (fun j : RepeatedIndex count => sectorEnergy j.1.val)
    rw [hsum] at hE
    have happrox : (∑ j : RepeatedIndex count, sectorEnergy j.1.val) / (m ^ 3 : ℕ) ≤
        (∑' k, p k * sectorEnergy k) + ε := by
      have hupper := (abs_lt.mp herr).2
      linarith
    exact le_trans (div_le_div_of_nonneg_right hE hM.le) happrox

/-- The physical canonical ground energy is the infimum over admissible states. -/
noncomputable def groundEnergy
    (energy : Set Space → State → ℝ)
    (admissible : Set Space → ℕ → State → Prop)
    (Ω : Set Space) (N : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ Γ : State, admissible Ω N Γ ∧ e = energy Ω Γ}

theorem groundEnergy_le
    (energy : Set Space → State → ℝ)
    (admissible : Set Space → ℕ → State → Prop)
    (Ω : Set Space) (N : ℕ)
    (hstable : BddBelow {e : ℝ | ∃ Γ : State, admissible Ω N Γ ∧ e = energy Ω Γ})
    (Γ : State) (hΓ : admissible Ω N Γ) :
    groundEnergy energy admissible Ω N ≤ energy Ω Γ := by
  exact csInf_le hstable ⟨Γ, hΓ, rfl⟩

/-- Canonicalization and the thermodynamic passage. The only convergence input
is the LN ground-energy limit on the explicitly constructed lattice domains.
All approximation weights, multiplicities, and canonical trial states are chosen
inside the proof. -/
theorem canonicalization_from_lattice_limit
    (R : ℕ → ℝ) (n : ℕ → ℕ) (p sectorEnergy : ℕ → ℕ → ℝ)
    (energy : Set Space → State → ℝ)
    (admissible : Set Space → ℕ → State → Prop)
    (ops : ∀ j, ReplicableBall State (R j) (n j) (sectorEnergy j) energy admissible)
    (hR : ∀ j, 0 < R j)
    (hp : ∀ j k, 0 ≤ p j k) (hpsum : ∀ j, Summable (p j))
    (hmeanSum : ∀ j, Summable (fun k : ℕ => (k : ℝ) * p j k))
    (henergySum : ∀ j, Summable (fun k => p j k * sectorEnergy j k))
    (hmass : ∀ j, ∑' k, p j k = 1)
    (hmean : ∀ j, ∑' k : ℕ, (k : ℝ) * p j k = n j)
    (hstable : ∀ j m, BddBelow {e : ℝ | ∃ Γ : State,
      admissible (latticeBalls (R j) m) (m ^ 3 * n j) Γ ∧
        e = energy (latticeBalls (R j) m) Γ})
    (eJ eU : ℝ)
    (hLN : ∀ m : ℕ → ℕ, (∀ j, 2 ≤ m j) →
      Tendsto (fun j => groundEnergy energy admissible (latticeBalls (R j) (m j))
        ((m j) ^ 3 * n j) / volume.real (latticeBalls (R j) (m j))) atTop (𝓝 eJ))
    (htrial : Tendsto (fun j => (∑' k, p j k * sectorEnergy j k) / ballVolume (R j))
      atTop (𝓝 eU)) : eJ ≤ eU := by
  classical
  have hV : ∀ j, 0 < ballVolume (R j) := by
    intro j
    unfold ballVolume
    have := hR j
    positivity
  have hex (j : ℕ) := exists_canonical_replication (R j) (n j) (p j) (sectorEnergy j)
    energy admissible (ops j) (hp j) (hpsum j) (hmeanSum j) (henergySum j)
    (hmass j) (hmean j) (ballVolume (R j) / ((j : ℝ) + 1)) (div_pos (hV j) (by positivity))
  choose m hm Γ hΓ hE using hex
  have hbound (j : ℕ) :
      groundEnergy energy admissible (latticeBalls (R j) (m j)) ((m j) ^ 3 * n j) /
        volume.real (latticeBalls (R j) (m j)) ≤
      (∑' k, p j k * sectorEnergy j k) / ballVolume (R j) + 1 / ((j : ℝ) + 1) := by
    have hg := groundEnergy_le energy admissible _ _ (hstable j (m j)) (Γ j) (hΓ j)
    have hmpos : 0 < m j := by have := hm j; omega
    have hM : (0 : ℝ) < ((m j) ^ 3 : ℕ) := by positivity
    have hraw :
        groundEnergy energy admissible (latticeBalls (R j) (m j)) ((m j) ^ 3 * n j) /
          ((m j) ^ 3 : ℕ) ≤
        (∑' k, p j k * sectorEnergy j k) + ballVolume (R j) / ((j : ℝ) + 1) :=
      le_trans (div_le_div_of_nonneg_right hg hM.le) (hE j)
    rw [latticeBalls_volume (R j) (hR j).le]
    have hdiv := div_le_div_of_nonneg_right hraw (hV j).le
    have hcast : (((m j) ^ 3 : ℕ) : ℝ) = (m j : ℝ) ^ 3 := by norm_cast
    rw [hcast] at hdiv
    calc
      _ = (groundEnergy energy admissible (latticeBalls (R j) (m j))
          ((m j) ^ 3 * n j) / (m j : ℝ) ^ 3) / ballVolume (R j) :=
        (div_div _ _ _).symm
      _ ≤ ((∑' k, p j k * sectorEnergy j k) + ballVolume (R j) / ((j : ℝ) + 1)) /
          ballVolume (R j) := hdiv
      _ = _ := by
        rw [add_div, div_right_comm (ballVolume (R j)) ((j : ℝ) + 1) (ballVolume (R j)),
          div_self (ne_of_gt (hV j))]
  have hzero : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper := htrial.add hzero
  rw [add_zero] at hupper
  exact le_of_tendsto_of_tendsto (hLN m hm) hupper (Eventually.of_forall hbound)

/-- The known Lieb--Narnhofer thermodynamic theorem, restricted to the
explicit sufficient domain data proved in `LNAdmissibility`. The radial
potential and energy representations in that data are identified with the
physical double layers by the classical Newton and polar integration formulas.
This literature input concerns canonical ground energies, never trial energies
or the new canonicalization comparison. -/
def LNThermodynamicLimit
    (energy : Set Space → State → ℝ)
    (admissible : Set Space → ℕ → State → Prop) (ρ eJ : ℝ) : Prop :=
  ∀ (R : ℕ → ℝ) (n m : ℕ → ℕ),
    (∀ j, ρ * ballVolume (R j) = (n j : ℝ)) →
    LatticeLNAdmissible R m →
    Tendsto (fun j => groundEnergy energy admissible (latticeBalls (R j) (m j))
      ((m j) ^ 3 * n j) / volume.real (latticeBalls (R j) (m j))) atTop (𝓝 eJ)

/-- The canonicalization lemma with the complete domain verification performed
inside Lean. Its only thermodynamic input is the known LN theorem. -/
theorem canonicalization
    (R : ℕ → ℝ) (n : ℕ → ℕ) (p sectorEnergy : ℕ → ℕ → ℝ)
    (energy : Set Space → State → ℝ)
    (admissible : Set Space → ℕ → State → Prop)
    (ops : ∀ j, ReplicableBall State (R j) (n j) (sectorEnergy j) energy admissible)
    (hRpos : ∀ j, 0 < R j) (hR : Tendsto R atTop atTop)
    (hp : ∀ j k, 0 ≤ p j k) (hpsum : ∀ j, Summable (p j))
    (hmeanSum : ∀ j, Summable (fun k : ℕ => (k : ℝ) * p j k))
    (henergySum : ∀ j, Summable (fun k => p j k * sectorEnergy j k))
    (hmass : ∀ j, ∑' k, p j k = 1)
    (hmean : ∀ j, ∑' k : ℕ, (k : ℝ) * p j k = n j)
    (hstable : ∀ j m, BddBelow {e : ℝ | ∃ Γ : State,
      admissible (latticeBalls (R j) m) (m ^ 3 * n j) Γ ∧
        e = energy (latticeBalls (R j) m) Γ})
    (ρ eJ eU : ℝ) (hcharge : ∀ j, ρ * ballVolume (R j) = (n j : ℝ))
    (hLN : LNThermodynamicLimit energy admissible ρ eJ)
    (htrial : Tendsto (fun j => (∑' k, p j k * sectorEnergy j k) / ballVolume (R j))
      atTop (𝓝 eU)) : eJ ≤ eU := by
  apply canonicalization_from_lattice_limit R n p sectorEnergy energy admissible ops hRpos
    hp hpsum hmeanSum henergySum hmass hmean hstable eJ eU _ htrial
  intro m hm
  exact hLN R n m hcharge (lattice_LN_admissible R m hRpos
    (fun j => Nat.le_trans (by decide : 1 ≤ 2) (hm j)) hR)

end Jellium.Canonicalization
