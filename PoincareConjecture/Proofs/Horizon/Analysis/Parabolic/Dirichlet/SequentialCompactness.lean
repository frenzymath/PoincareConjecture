import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences








set_option autoImplicit false

open Set UniformSpace

namespace Poincare.Analysis.Dirichlet

variable {V H : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]


theorem isCompactOperator_of_cauchySeq_subseq (j : V →L[ℝ] H)
    (hj : ∀ u : ℕ → V, (∀ k, ‖u k‖ ≤ 1) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (j ∘ u ∘ φ)) :
    IsCompactOperator j := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    j.toLinearMap zero_lt_one).mpr
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  intro U hU
  by_contra h
  push Not at h
  obtain ⟨v, hv, hsep⟩ : ∃ v : ℕ → H,
      (∀ k, v k ∈ j '' Metric.closedBall 0 1) ∧
        ∀ k l, l < k → v l ∉ UniformSpace.ball (v k) U := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using!
      seq_of_forall_finite_exists h
  choose u hu hju using hv
  obtain ⟨φ, hφ, hc⟩ := hj u (fun k => by simpa using hu k)
  obtain ⟨N, hN⟩ := hc.mem_entourage hU
  apply hsep (φ (N + 1)) (φ N) (hφ (Nat.lt_add_one N))
  simpa only [Function.comp_apply, hju, UniformSpace.ball, mem_preimage] using
    hN (N + 1) N N.le_succ le_rfl

end Poincare.Analysis.Dirichlet
