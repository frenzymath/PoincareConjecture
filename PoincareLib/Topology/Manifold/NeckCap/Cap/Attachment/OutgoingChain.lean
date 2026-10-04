import PoincareLib.Topology.Manifold.NeckCap.Cap.Attachment.FiniteChain
import PoincareLib.Topology.Manifold.NeckCap.Cap.Attachment.ForwardChain
import PoincareLib.Topology.Manifold.NeckCap.Cap.Chain.Shape

/-!
# Capped tubes on outgoing selected chains

An outgoing chain is finite or forward-infinite. Both actual cylinder
constructions retain the given chain and combine with the cap attachment.

Reference: Morgan--Tian, Proposition A.21, pp. 510--513.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

/-- Every sufficiently small outgoing selected chain produces a capped
tube on its exact union with the original cap. -/
theorem exists_outgoing_capped_tube_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T →
          ∃ A : CappedTubeCertificate g, A.cap = C ∧
            A.tube.epsilon = C.epsilon ∧ HEq A.tube.chain T ∧
            A.carrier = C.carrier ∪ (T.unionOpen : Set M) := by
  obtain ⟨ε₁, hε₁, hsmall, hfinite⟩ := exists_finite_capped_tube_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hforward⟩ := exists_forward_capped_tube_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε H T hT
  have hcenters : ∀ j ∈ T.shape.active, 0 < j → (T.neck j).center ∉ C.carrier :=
    fun j hj hpos => (hT.centers j hj hpos).2
  rcases hT.shape_eq_finite_or_forward with ⟨b, hshape⟩ | hshape
  · exact hfinite C (hε.trans (min_le_left _ _)) T 0 b hshape hT.first_neck hcenters
  · exact hforward C (hε.trans (min_le_right _ _)) T 0 hshape hT.first_neck hcenters

end PoincareMT.CapCertificate
