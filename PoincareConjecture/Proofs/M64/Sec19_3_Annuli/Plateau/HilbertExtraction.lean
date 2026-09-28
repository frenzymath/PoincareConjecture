import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import Mathlib.MeasureTheory.Measure.SeparableMeasure











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness



theorem m64SeparableHilbert_weak_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) {R : ℝ} (hR : ∀ j, ‖u j‖ ≤ R) :
    ∃ (v : H) (k : ℕ → ℕ), StrictMono k ∧ WeakConverges (fun j => u (k j)) v := by
  let a (j : ℕ) : WeakDual ℝ H := StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) (u j))
  have ha (j : ℕ) : a j ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R := by
    change dist ((InnerProductSpace.toDual ℝ H) (u j)) 0 ≤ R
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hR j
  obtain ⟨L, -, k, hk, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ H 0 R) ha
  let v : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual L)
  refine ⟨v, k, hk, ?_⟩
  intro A
  let z := (InnerProductSpace.toDual ℝ H).symm A
  have hz := tendsto_iff_forall_eval_tendsto_topDualPairing.mp hlim z
  change Tendsto (fun j => ((InnerProductSpace.toDual ℝ H) (u (k j))) z)
    atTop (𝓝 ((WeakDual.toStrongDual L) z)) at hz
  have heq (x : H) : (InnerProductSpace.toDual ℝ H) x z = A x := by
    rw [InnerProductSpace.toDual_apply_apply, real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hv : (WeakDual.toStrongDual L) z = A v := by
    rw [← (InnerProductSpace.toDual ℝ H).apply_symm_apply (WeakDual.toStrongDual L)]
    exact heq v
  simpa only [heq, hv] using hz

end PoincareConjecture
