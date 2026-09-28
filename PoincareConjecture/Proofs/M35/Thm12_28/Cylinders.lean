import PoincareConjecture.Proofs.M35.Thm12_28.GeneralizedFlow
import PoincareConjecture.Definitions.M13TimeRescaling
import Mathlib.Topology.Order.MonotoneContinuity









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization



theorem clock_embedding {J I : Set ℝ} {a Q : ℝ} (hQ : 0 < Q)
    (htime : ∀ s ∈ I, a + s / Q ∈ J) :
    Topology.IsEmbedding (fun s : I => (⟨a + s.val / Q, htime s.val s.property⟩ : J)) := by
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact (parabolicTimeOrderIso Q hQ a).symm.toHomeomorph.isEmbedding.comp
    Topology.IsEmbedding.subtypeVal



noncomputable def cylinder {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (a Q : ℝ) (hQ : 0 < Q) (I : Set ℝ) (U : Set StandardCapSpace)
    (htime : ∀ s ∈ I, a + s / Q ∈ J) :
    GeneralizedFlowCylinder (generalizedFlow F) capCarrier a Q I U where
  scale_pos := hQ
  forward s hs := (sliceDiffeomorph (htime s hs)).symm
  inverse s hs := sliceDiffeomorph (htime s hs)
  forward_smooth s hs := (sliceDiffeomorph (htime s hs)).symm.contMDiff.contMDiffOn
  inverse_smooth s hs := (sliceDiffeomorph (htime s hs)).contMDiff.contMDiffOn
  left_inverse s hs _ _ := (sliceDiffeomorph (htime s hs)).apply_symm_apply _
  right_inverse s hs _ _ := (sliceDiffeomorph (htime s hs)).symm_apply_apply _
  embedding := by
    let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
    exact (spacetimeHomeomorph J).symm.isEmbedding.comp
      ((clock_embedding hQ htime).prodMap Topology.IsEmbedding.subtypeVal)
  vertical_compatibility _ _ x _ := by
    refine ⟨(), x, 1, zero_lt_one, ?_⟩
    intro s hs _
    exact ⟨htime s hs, rfl⟩



theorem cylinder_pullbackInner {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (a Q : ℝ) (hQ : 0 < Q) (I : Set ℝ) (U : Set StandardCapSpace)
    (htime : ∀ s ∈ I, a + s / Q ∈ J) (s : ℝ) (hs : s ∈ I)
    (x : StandardCapSpace) (v w : TangentSpace (𝓡 3) x) :
    (cylinder F a Q hQ I U htime).pullbackInner s hs x v w =
      Q * (F.metric (a + s / Q)).inner x v w := by
  exact congrArg (fun r : ℝ => Q * r) (metric_pullback F (htime s hs) x v w)

end PoincareConjecture.M35.OrdinaryRealization
