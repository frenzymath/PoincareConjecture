import PoincareConjecture.Proofs.M32.Claim11_34.CylinderOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

noncomputable def blowup_sliceEmbedding (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) (t : ℝ) (htk : t ∈ Icc (-G.exhaustion.time k) 0) :
    OpenPartialHomeomorph G.limit.carrier.carrier
      ((S.flow (G.subsequence k)).slice
        ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).carrier where
  toFun := (G.embedding k).forward t htk
  invFun := (G.embedding k).inverse t htk
  source := G.exhaustion.space k
  target := (G.embedding k).forward t htk '' G.exhaustion.space k
  map_source' := fun x hx => mem_image_of_mem _ hx
  map_target' := by
    rintro x ⟨y, hy, rfl⟩
    rw [(G.embedding k).left_inverse t htk hy]
    exact hy
  left_inv' := (G.embedding k).left_inverse t htk
  right_inv' := (G.embedding k).right_inverse t htk
  open_source := G.exhaustion.space_open k
  open_target := cylinder_isOpen_forward_image (G.embedding k)
    (G.exhaustion.space_open k) t htk
  continuousOn_toFun := ((G.embedding k).forward_smooth t htk).continuousOn
  continuousOn_invFun := ((G.embedding k).inverse_smooth t htk).continuousOn

theorem blowup_sliceEmbedding_smooth (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) (t : ℝ) (htk : t ∈ Icc (-G.exhaustion.time k) 0) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (blowup_sliceEmbedding G k t htk)
        (G.exhaustion.space k) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (blowup_sliceEmbedding G k t htk).symm
        (blowup_sliceEmbedding G k t htk).target :=
  ⟨(G.embedding k).forward_smooth t htk, (G.embedding k).inverse_smooth t htk⟩

end PoincareConjecture.M32
