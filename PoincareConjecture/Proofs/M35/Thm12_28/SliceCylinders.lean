import PoincareConjecture.Proofs.M35.Thm12_28.Cylinders
import PoincareConjecture.Proofs.M35.Thm12_28.SliceGeometry









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization



noncomputable def sliceCylinder {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {a : ℝ} (ha : a ∈ J) (Q : ℝ) (hQ : 0 < Q) (I : Set ℝ)
    (U : Set (slice J a).carrier) (htime : ∀ s ∈ I, a + s / Q ∈ J) :
    GeneralizedFlowCylinder (generalizedFlow F) (slice J a) a Q I U where
  scale_pos := hQ
  forward s hs x := (sliceDiffeomorph (htime s hs)).symm (sliceDiffeomorph ha x)
  inverse s hs y := (sliceDiffeomorph ha).symm (sliceDiffeomorph (htime s hs) y)
  forward_smooth s hs := ((sliceDiffeomorph (htime s hs)).symm.contMDiff.comp
    (sliceDiffeomorph ha).contMDiff).contMDiffOn
  inverse_smooth s hs := ((sliceDiffeomorph ha).symm.contMDiff.comp
    (sliceDiffeomorph (htime s hs)).contMDiff).contMDiffOn
  left_inverse _ _ _ _ := rfl
  right_inverse _ _ _ _ := rfl
  embedding := by
    let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
    exact (spacetimeHomeomorph J).symm.isEmbedding.comp
      ((clock_embedding hQ htime).prodMap
        ((sliceDiffeomorph ha).toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal))
  vertical_compatibility _ _ x _ := by
    refine ⟨(), x.val, 1, zero_lt_one, ?_⟩
    intro s hs _
    exact ⟨htime s hs, rfl⟩



theorem sliceCylinder_pointMap {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {a : ℝ} (ha : a ∈ J) (Q : ℝ) (hQ : 0 < Q) (I : Set ℝ)
    (U : Set (slice J a).carrier) (htime : ∀ s ∈ I, a + s / Q ∈ J)
    (s : ℝ) (hs : s ∈ I) (x : (slice J a).carrier) :
    (sliceCylinder F ha Q hQ I U htime).pointMap s hs x =
      (⟨a + s / Q, ⟨x.val, htime s hs⟩⟩ : (generalizedFlow F).point) := rfl



theorem sliceCylinder_zero_identity {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {a : ℝ} (ha : a ∈ J) (Q : ℝ) (hQ : 0 < Q) (I : Set ℝ)
    (U : Set (slice J a).carrier) (htime : ∀ s ∈ I, a + s / Q ∈ J)
    (h₀ : 0 ∈ I) (x : (slice J a).carrier) :
    (sliceCylinder F ha Q hQ I U htime).pointMap 0 h₀ x =
      (⟨a, x⟩ : (generalizedFlow F).point) := by
  rcases x with ⟨x, hx⟩
  change a ∈ J at hx
  change (⟨a + 0 / Q, ⟨x, htime 0 h₀⟩⟩ : Σ t : ℝ, {_x : StandardCapSpace // t ∈ J}) =
    ⟨a, ⟨x, hx⟩⟩
  apply (spacetimeEquiv J).injective
  change ((⟨a + 0 / Q, htime 0 h₀⟩ : J), x) = ((⟨a, hx⟩ : J), x)
  congr 1
  exact Subtype.ext (by simp only [zero_div, add_zero])



theorem sliceCylinder_curvatureNorm (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {a : ℝ} (ha : a ∈ J) (Q : ℝ) (hQ : 0 < Q) (I : Set ℝ)
    (U : Set (slice J a).carrier) (htime : ∀ s ∈ I, a + s / Q ∈ J)
    (s : ℝ) (hs : s ∈ I) (x : (slice J a).carrier) :
    (generalizedFlow F).curvatureNorm ((sliceCylinder F ha Q hQ I U htime).pointMap s hs x) =
      (F.connection (a + s / Q)).curvatureTensorNorm x.val :=
  curvatureNorm_eq P F (htime s hs) x.val

end PoincareConjecture.M35.OrdinaryRealization
