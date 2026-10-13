import Jellium.Lower
import Jellium.Upper
import Jellium.Localization

/-!
The initial abstract scalar reduction, retained for comparison. Its structures
describe construction obligations and are not literature inputs. This file by
itself does not prove Conjecture 5.1. The connected physical proof is now in
LowerPhysical, UpperPhysical and Conjecture51 and does not use these structures.
-/

open Filter Topology

namespace Jellium

/-- Abstract normalized-sequence obligations from the initial reduction. The
physical sequence is constructed separately in LowerPhysical. -/
structure LowerConstructionObligations (eJ eU : ℝ) where
  trial : ℕ → ℝ
  canonicalEnergy : ℕ → ℝ
  error : ℕ → ℝ
  trial_limit : Tendsto trial atTop (𝓝 eU)
  canonical_limit : Tendsto canonicalEnergy atTop (𝓝 eJ)
  error_limit : Tendsto error atTop (𝓝 0)
  comparison : ∀ᶠ n in atTop, canonicalEnergy n ≤ trial n + error n

/-- Normalized energies of one fixed packing, after its large-box limit.
`bulk_lower` is the conclusion of the new bounded-layer construction.
`variational` needs a genuine averaged quantum state with the claimed density.
`trial_upper` needs the spatial core/fluid construction and its energy estimate.
All three remain explicit obligations here.
-/
structure UpperConstructionObligations (eJ eU K ε : ℝ) where
  θ : ℝ
  collarError : ℝ
  densityEnergy : ℕ → ℝ
  trialEnergy : ℕ → ℝ
  coverage : 1 - ε ≤ θ
  disjoint_volume : θ ≤ 1
  collar_small : collarError ≤ ε
  bulk_lower : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, eU - η ≤ densityEnergy n
  variational : ∀ᶠ n in atTop, densityEnergy n ≤ trialEnergy n
  trial_upper : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
    trialEnergy n ≤ θ * (eJ + ε) + K * (1 - θ) + collarError + η

/-- The lower and upper eventual inequalities really imply the fixed-packing
bound. In particular they use the same density and same trial-energy sequence. -/
theorem fixed_packing_bound {eJ eU K ε : ℝ}
    (h : UpperConstructionObligations eJ eU K ε) :
    eU ≤ h.θ * (eJ + ε) + K * (1 - h.θ) + h.collarError := by
  by_contra hnot
  let B := h.θ * (eJ + ε) + K * (1 - h.θ) + h.collarError
  have hgap : 0 < eU - B := sub_pos.mpr (lt_of_not_ge hnot)
  let η := (eU - B) / 3
  have hη : 0 < η := div_pos hgap (by norm_num)
  obtain ⟨n, hlo, hvar, hup⟩ :=
    ((h.bulk_lower η hη).and (h.variational.and (h.trial_upper η hη))).exists
  dsimp [η, B] at *
  linarith

/-- Conditional reduction only. Its unproved construction arguments contain
the new analytical and geometric work, which is not covered merely by allowing
well-known literature results. The scalars are not defined as physical energies
anywhere in this project.
-/
theorem equality_of_construction_obligations {eJ eU K : ℝ}
    (hK : 0 ≤ K)
    (lower : LowerConstructionObligations eJ eU)
    (upper : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Nonempty (UpperConstructionObligations eJ eU K ε)) :
    eJ = eU := by
  apply le_antisymm
  · exact lower_comparison_of_sequences eJ eU lower.trial lower.canonicalEnergy
      lower.error lower.trial_limit lower.canonical_limit lower.error_limit lower.comparison
  · apply Upper.upper_le_of_trial_bounds hK
    intro ε hε hε1
    obtain ⟨h⟩ := upper ε hε hε1
    exact ⟨h.θ, h.collarError, h.coverage, h.disjoint_volume, h.collar_small,
      fixed_packing_bound h⟩

end Jellium
