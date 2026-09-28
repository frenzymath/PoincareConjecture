import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.Variational
import Mathlib.Analysis.Normed.Operator.Compact.Basic









set_option autoImplicit false

noncomputable section

open Set UniformSpace Metric Topology

namespace Poincare.Analysis.Dirichlet

variable {V H : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


theorem isCompactOperator_completionMap (j : V →L[ℝ] H)
    (hj : IsCompactOperator j) : IsCompactOperator (completionMap j) := by
  obtain ⟨K, hK, hsub⟩ := hj.image_closedBall_subset_compact (f := j.toLinearMap) 1
  refine (isCompactOperator_iff_image_ball_subset_compact
    (completionMap j).toLinearMap zero_lt_one).mpr ⟨K, hK, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hclosed : IsClosed {v : Completion V | ‖v‖ < 1 → completionMap j v ∈ K} := by
    have heq : {v : Completion V | ‖v‖ < 1 → completionMap j v ∈ K} =
        {v | 1 ≤ ‖v‖} ∪ (completionMap j) ⁻¹' K := by
      ext v
      simp only [mem_ofPred_eq, mem_union, mem_preimage, imp_iff_not_or, not_lt]
    rw [heq]
    exact ((isClosed_le continuous_const continuous_norm).union
        (hK.isClosed.preimage (completionMap j).continuous))
  have hall : ∀ v : Completion V, ‖v‖ < 1 → completionMap j v ∈ K := by
    intro v
    induction v using Completion.induction_on with
    | hp => exact hclosed
    | ih v =>
      intro hv
      rw [completionMap_coe]
      exact hsub ⟨v, by simpa using hv.le, rfl⟩
  exact hall u (by simpa using hu)

end Poincare.Analysis.Dirichlet
