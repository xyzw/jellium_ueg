import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-! Independent sampling identities used by the local orbital construction.
The sampling law is the concrete finite product of the one-particle law.
The pair sum omits equal indices, producing the negative self correction. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped BigOperators
open Classical

namespace Jellium.OrbitalSampling

variable {α : Type*} [MeasurableSpace α]

noncomputable def sampleMeasure (ν : Measure α) (n : ℕ) : Measure (Fin n → α) :=
  Measure.pi (fun _ => ν)

instance sampleMeasure_probability (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (sampleMeasure ν n) := by
  unfold sampleMeasure
  infer_instance

noncomputable def oneBodySum {n : ℕ} (v : α → ℝ) (x : Fin n → α) : ℝ :=
  ∑ i, v (x i)

noncomputable def pairSum {n : ℕ} (k : α → α → ℝ) (x : Fin n → α) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i, k (x i) (x j)) / 2

noncomputable def classicalEnergy {n : ℕ}
    (k : α → α → ℝ) (v : α → ℝ) (B : ℝ) (x : Fin n → α) : ℝ :=
  pairSum k x + oneBodySum v x + B

variable (ν : Measure α) [IsProbabilityMeasure ν] {n : ℕ}

theorem eval_measurePreserving (i : Fin n) :
    MeasurePreserving (fun x : Fin n → α => x i) (sampleMeasure ν n) ν :=
  measurePreserving_eval (fun _ => ν) i

/-- All centers obey any almost-sure one-particle constraint. -/
theorem ae_all_coordinates {p : α → Prop} (hp : ∀ᵐ x ∂ν, p x) :
    ∀ᵐ x : Fin n → α ∂sampleMeasure ν n, ∀ i, p (x i) :=
  ae_all_iff.mpr (fun i => (eval_measurePreserving ν i).quasiMeasurePreserving.ae hp)

theorem pair_measurePreserving {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin n → α => (x i, x j))
      (sampleMeasure ν n) (ν.prod ν) := by
  refine ⟨by fun_prop, ?_⟩
  have h := (iIndepFun_pi (μ := fun _ : Fin n => ν)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have hm := h.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  change (sampleMeasure ν n).map (fun x => (x i, x j)) =
    ((sampleMeasure ν n).map (fun x => x i)).prod
      ((sampleMeasure ν n).map (fun x => x j)) at hm
  rw [(eval_measurePreserving ν i).map_eq, (eval_measurePreserving ν j).map_eq] at hm
  exact hm

omit [IsProbabilityMeasure ν] in
private theorem integral_comp_preserving {β : Type*} [MeasurableSpace β]
    {μ : Measure β} {f : β → α} (hf : MeasurePreserving f μ ν)
    {v : α → ℝ} (hv : Integrable v ν) :
    (∫ x, v (f x) ∂μ) = ∫ y, v y ∂ν := by
  have hv' : AEStronglyMeasurable v (μ.map f) := by
    rw [hf.map_eq]
    exact hv.aestronglyMeasurable
  rw [← integral_map hf.measurable.aemeasurable hv', hf.map_eq]

theorem integrable_eval {v : α → ℝ} (hv : Integrable v ν) (i : Fin n) :
    Integrable (fun x : Fin n → α => v (x i)) (sampleMeasure ν n) :=
  (eval_measurePreserving ν i).integrable_comp_of_integrable hv

theorem integral_eval {v : α → ℝ} (hv : Integrable v ν) (i : Fin n) :
    (∫ x : Fin n → α, v (x i) ∂sampleMeasure ν n) = ∫ y, v y ∂ν := by
  exact integral_comp_preserving ν (eval_measurePreserving ν i) hv

theorem integrable_pair {k : α → α → ℝ}
    (hk : Integrable (Function.uncurry k) (ν.prod ν)) {i j : Fin n} (hij : i ≠ j) :
    Integrable (fun x : Fin n → α => k (x i) (x j)) (sampleMeasure ν n) :=
  (pair_measurePreserving ν hij).integrable_comp_of_integrable hk

theorem integral_pair {k : α → α → ℝ}
    (hk : Integrable (Function.uncurry k) (ν.prod ν)) {i j : Fin n} (hij : i ≠ j) :
    (∫ x : Fin n → α, k (x i) (x j) ∂sampleMeasure ν n) =
      ∫ x, ∫ y, k x y ∂ν ∂ν := by
  calc
    _ = ∫ z, Function.uncurry k z ∂ν.prod ν :=
      integral_comp_preserving (ν.prod ν) (pair_measurePreserving ν hij) hk
    _ = _ := integral_prod (Function.uncurry k) hk

theorem integrable_oneBodySum {v : α → ℝ} (hv : Integrable v ν) :
    Integrable (oneBodySum (n := n) v) (sampleMeasure ν n) :=
  integrable_finsetSum _ (fun i _ => integrable_eval ν hv i)

theorem integral_oneBodySum {v : α → ℝ} (hv : Integrable v ν) :
    (∫ x : Fin n → α, oneBodySum v x ∂sampleMeasure ν n) =
      (n : ℝ) * ∫ y, v y ∂ν := by
  simp only [oneBodySum, integral_finsetSum _ (fun i _ => integrable_eval ν hv i),
    integral_eval ν hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem integrable_pairSum {k : α → α → ℝ}
    (hk : Integrable (Function.uncurry k) (ν.prod ν)) :
    Integrable (pairSum (n := n) k) (sampleMeasure ν n) := by
  exact (integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j hj => integrable_pair ν hk (Finset.ne_of_mem_erase hj).symm))).div_const 2

theorem integral_pairSum {k : α → α → ℝ}
    (hk : Integrable (Function.uncurry k) (ν.prod ν)) :
    (∫ x : Fin n → α, pairSum k x ∂sampleMeasure ν n) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 * (∫ x, ∫ y, k x y ∂ν ∂ν) := by
  unfold pairSum
  rw [integral_div]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j hj => integrable_pair ν hk (Finset.ne_of_mem_erase hj).symm))]
  simp_rw [integral_finsetSum _ (fun j hj =>
    integrable_pair ν hk (Finset.ne_of_mem_erase hj).symm)]
  have hi (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i,
        ∫ x : Fin n → α, k (x i) (x j) ∂sampleMeasure ν n) =
          ((n : ℝ) - 1) * (∫ x, ∫ y, k x y ∂ν ∂ν) := by
    rw [Finset.sum_congr rfl (fun j hj =>
      integral_pair ν hk (Finset.ne_of_mem_erase hj).symm)]
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub (by have := i.isLt; omega)]
    norm_num
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integrable_classicalEnergy {k : α → α → ℝ} {v : α → ℝ}
    (hk : Integrable (Function.uncurry k) (ν.prod ν)) (hv : Integrable v ν) (B : ℝ) :
    Integrable (classicalEnergy (n := n) k v B) (sampleMeasure ν n) :=
  ((integrable_pairSum ν hk).add (integrable_oneBodySum ν hv)).add (integrable_const B)

/-- Exact expectation, including the omitted self-interaction. -/
theorem integral_classicalEnergy {k : α → α → ℝ} {v : α → ℝ}
    (hk : Integrable (Function.uncurry k) (ν.prod ν)) (hv : Integrable v ν) (B : ℝ) :
    (∫ x : Fin n → α, classicalEnergy k v B x ∂sampleMeasure ν n) =
      (n : ℝ) ^ 2 / 2 * (∫ x, ∫ y, k x y ∂ν ∂ν) +
      (n : ℝ) * (∫ x, v x ∂ν) + B -
      (n : ℝ) / 2 * (∫ x, ∫ y, k x y ∂ν ∂ν) := by
  unfold classicalEnergy
  have hs : Integrable (fun x : Fin n → α => pairSum k x + oneBodySum v x)
      (sampleMeasure ν n) :=
    (integrable_pairSum ν hk).add (integrable_oneBodySum ν hv)
  rw [integral_add hs (integrable_const B),
    integral_add (integrable_pairSum (n := n) ν hk) (integrable_oneBodySum ν hv),
    integral_pairSum ν hk, integral_oneBodySum ν hv]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

theorem integral_pairSum_le {k : α → α → ℝ} {C : ℝ}
    (hk : Integrable (Function.uncurry k) (ν.prod ν))
    (hC : (∫ x, ∫ y, k x y ∂ν ∂ν) ≤ C) :
    (∫ x : Fin n → α, pairSum k x ∂sampleMeasure ν n) ≤
      (n : ℝ) * ((n : ℝ) - 1) / 2 * C := by
  rw [integral_pairSum ν hk]
  apply mul_le_mul_of_nonneg_left hC
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    positivity

/-- An atomless law yields distinct centers almost surely. -/
theorem ae_injective [MeasurableEq α] [NullSingletonClass ν] :
    ∀ᵐ x : Fin n → α ∂sampleMeasure ν n, Function.Injective x := by
  have hp : ∀ᵐ z : α × α ∂ν.prod ν, z.1 ≠ z.2 := by
    apply (ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
    exact Filter.Eventually.of_forall (fun x => (ν.ae_ne x).mono (fun _ h => h.symm))
  have hpair (i j : Fin n) : ∀ᵐ x : Fin n → α ∂sampleMeasure ν n,
      i ≠ j → x i ≠ x j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · have hmp := pair_measurePreserving ν hij
      have hp' : ∀ᵐ z ∂(sampleMeasure ν n).map (fun x => (x i, x j)), z.1 ≠ z.2 := by
        rw [hmp.map_eq]
        exact hp
      exact (ae_of_ae_map hmp.measurable.aemeasurable hp').mono (fun _ h _ => h)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpair i))] with x hx
  intro i j hij
  by_contra hne
  exact hx i j hne hij

end Jellium.OrbitalSampling
