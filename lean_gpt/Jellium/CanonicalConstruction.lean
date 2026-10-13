import Jellium.Canonical

/-!
Construction of an exactly canonical mixture from a finite list of radial ball
states. The quantum operations below are the standard disjoint-support fermionic
product and finite mixture operations. Their energy law is the exact Newton/Fock
identity, including all charged cross terms. The energy comparison and the
canonical assignment construction are derived, not supplied as operation laws.
-/

open scoped BigOperators

namespace Jellium.CanonicalConstruction

variable (I State : Type*) [Fintype I] [DecidableEq I]

/-- Standard operations on finite-energy states in disjoint equal-radius balls.
`availableSector k` records that the chosen radial, Dirichlet `k`-particle state
exists, and `sectorEnergy k` is its Jellium energy in one ball. The `reference`
is the integer background charge in each ball. The distance weights in the
charged product identity are inverse center distances for unordered pairs.

No thermodynamic conclusion or nonpositive cross-energy conclusion is assumed.
-/
structure FermionBallOperations where
  reference : ℕ
  sectorEnergy : ℕ → ℝ
  availableSector : ℕ → Prop
  energy : State → ℝ
  canonical : ℕ → State → Prop
  pairs : Finset (I × I)
  distanceWeight : I × I → ℝ
  pairs_distinct : ∀ ij ∈ pairs, ij.2 ≠ ij.1
  distanceWeight_nonnegative : ∀ ij ∈ pairs, 0 ≤ distanceWeight ij
  product : (I → ℕ) → State
  product_canonical : ∀ k : I → ℕ,
    (∀ i, availableSector (k i)) → canonical (∑ i, k i) (product k)
  product_energy : ∀ k : I → ℕ,
    (∀ i, availableSector (k i)) →
    energy (product k) = (∑ i, sectorEnergy (k i)) +
      ∑ ij ∈ pairs, distanceWeight ij *
        (((k ij.1 : ℝ) - reference) * ((k ij.2 : ℝ) - reference))
  mixture : (Equiv.Perm I → ℝ) → (Equiv.Perm I → State) → State
  mixture_canonical : ∀ (p : Equiv.Perm I → ℝ) (states : Equiv.Perm I → State)
    (N : ℕ), (∀ σ, 0 ≤ p σ) → (∑ σ, p σ = 1) →
    (∀ σ, canonical N (states σ)) → canonical N (mixture p states)
  mixture_energy : ∀ (p : Equiv.Perm I → ℝ) (states : Equiv.Perm I → State),
    (∀ σ, 0 ≤ p σ) → (∑ σ, p σ = 1) →
    energy (mixture p states) = ∑ σ, p σ * energy (states σ)

variable {I State}

/-- Explicit fixed-multiplicity trial state, averaged over every permutation. -/
noncomputable def uniformPermutationState (ops : FermionBallOperations I State)
    (sectors : I → ℕ) : State :=
  ops.mixture Canonical.permutationWeight
    (fun σ => ops.product (fun i => sectors (σ i)))

/-- Every product and hence its mixture has exactly the list's total particle count. -/
theorem uniformPermutationState_canonical (ops : FermionBallOperations I State)
    (sectors : I → ℕ) (havailable : ∀ i, ops.availableSector (sectors i)) :
    ops.canonical (∑ i, sectors i) (uniformPermutationState ops sectors) := by
  unfold uniformPermutationState
  apply ops.mixture_canonical _ _ _
    Canonical.permutationWeight_nonnegative Canonical.permutationWeight_normalized
  intro σ
  have hprod := ops.product_canonical (fun i => sectors (σ i)) (fun i => havailable (σ i))
  simpa only [Equiv.sum_comp] using hprod

/-- The specified integer mean makes every product exactly neutral. -/
theorem uniformPermutationState_neutral (ops : FermionBallOperations I State)
    (sectors : I → ℕ) (havailable : ∀ i, ops.availableSector (sectors i))
    (hneutral : ∑ i, sectors i = Fintype.card I * ops.reference) :
    ops.canonical (Fintype.card I * ops.reference)
      (uniformPermutationState ops sectors) := by
  rw [← hneutral]
  exact uniformPermutationState_canonical ops sectors havailable

/-- The new canonicalization comparison for the constructed finite mixture.
The nonpositive interaction is derived from the permutation law. -/
theorem uniformPermutationState_energy_le (ops : FermionBallOperations I State)
    (sectors : I → ℕ) (havailable : ∀ i, ops.availableSector (sectors i))
    (hcard : 1 < Fintype.card I)
    (hneutral : ∑ i, sectors i = Fintype.card I * ops.reference) :
    ops.energy (uniformPermutationState ops sectors) ≤ ∑ i, ops.sectorEnergy (sectors i) := by
  let q : I → ℝ := fun i => (sectors i : ℝ) - ops.reference
  have hq : ∑ i, q i = 0 := by
    have hreal : (∑ i, (sectors i : ℝ)) =
        (Fintype.card I : ℝ) * (ops.reference : ℝ) := by exact_mod_cast hneutral
    simp only [q, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    linarith
  have hcross := Canonical.permutation_cross_interaction_nonpositive q hq hcard
    ops.pairs ops.distanceWeight ops.pairs_distinct ops.distanceWeight_nonnegative
  have hlocal :
      (∑ σ : Equiv.Perm I, Canonical.permutationWeight σ *
        ∑ i, ops.sectorEnergy (sectors (σ i))) = ∑ i, ops.sectorEnergy (sectors i) := by
    have hsum (σ : Equiv.Perm I) :
        (∑ i, ops.sectorEnergy (sectors (σ i))) = ∑ i, ops.sectorEnergy (sectors i) :=
      Equiv.sum_comp σ (fun i => ops.sectorEnergy (sectors i))
    simp_rw [hsum]
    rw [← Finset.sum_mul, Canonical.permutationWeight_normalized, one_mul]
  have henergy : ops.energy (uniformPermutationState ops sectors) =
      (∑ i, ops.sectorEnergy (sectors i)) +
      (∑ σ : Equiv.Perm I, Canonical.permutationWeight σ *
        ∑ ij ∈ ops.pairs, ops.distanceWeight ij *
          (Canonical.permutationCharge q σ ij.1 *
            Canonical.permutationCharge q σ ij.2)) := by
    unfold uniformPermutationState
    rw [ops.mixture_energy _ _ Canonical.permutationWeight_nonnegative
      Canonical.permutationWeight_normalized]
    have heach (σ : Equiv.Perm I) :=
      ops.product_energy (fun i => sectors (σ i)) (fun i => havailable (σ i))
    simp_rw [heach, mul_add, Finset.sum_add_distrib]
    rw [hlocal]
    rfl
  rw [henergy]
  exact add_le_of_nonpos_right hcross

/-- The construction supplies an actual state together with both desired properties. -/
theorem exists_neutral_state_energy_le (ops : FermionBallOperations I State)
    (sectors : I → ℕ) (havailable : ∀ i, ops.availableSector (sectors i))
    (hcard : 1 < Fintype.card I)
    (hneutral : ∑ i, sectors i = Fintype.card I * ops.reference) :
    ∃ Γ : State, ops.canonical (Fintype.card I * ops.reference) Γ ∧
      ops.energy Γ ≤ ∑ i, ops.sectorEnergy (sectors i) :=
  ⟨uniformPermutationState ops sectors,
    uniformPermutationState_neutral ops sectors havailable hneutral,
    uniformPermutationState_energy_le ops sectors havailable hcard hneutral⟩

end Jellium.CanonicalConstruction
