import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B in
theorem terminal_no_two_sided_projective_plane (Q : SingularLimitConclusion H) :
    SurgeryNoTwoSidedProjectivePlane (Q.extension.extended.slice T) := by
  rintro ⟨f, hf⟩
  let t : Ico H.reference.tMinus T := ⟨H.reference.tMinus, le_rfl, H.reference.tMinus_lt⟩
  have ht : t.val ∈ F.time_domain := I.last_slab.time_subset
    ⟨B.reference_start_lt.le, H.reference.tMinus_lt⟩
  exact F.no_two_sided_projective_plane t.val ht
    ⟨(B.reference_identify t).symm ∘ Q.terminal_source ∘ f,
      (B.reference_identify t).symm.toHomeomorph.isOpenEmbedding.comp
        (Q.terminal_source_openEmbedding.comp hf)⟩

end PoincareConjecture.RepairedContinuationLimitBridge
