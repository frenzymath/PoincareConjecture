import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

variable {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_terminal_scalar_bound_of_compactSpace [CompactSpace M]
    (F : RicciFlow 3 M (Iic 0)) (P : M23NormalizedKappaCompactnessPredecessors) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : M, (F.connection 0).scalarCurvature x ≤ B := by
  have hcont : Continuous (F.connection 0).scalarCurvature := by
    apply continuousOn_univ.mp
    exact (P.scalar_regular M (Iic 0) F).continuousOn.comp
      (f := fun x : M => (0, x))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨by simp, mem_univ x⟩)
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hcont.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x =>
    (hB (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)⟩

end PoincareConjecture.RicciFlow
