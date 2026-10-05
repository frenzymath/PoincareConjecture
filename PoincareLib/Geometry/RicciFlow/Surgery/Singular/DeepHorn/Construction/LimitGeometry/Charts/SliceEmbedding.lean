import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.LimitGeometry.Charts.CylinderOpen

/-!
# The actual included-time slice embedding

Morgan--Tian Claims 11.34-11.35, printed pp. 288-290, and the original
scale/time convention of Definition 3.40, printed p. 61. This packages
the retained cylinder maps at the literal original time a+t/Q.
It rederives the fixed-time part of the read-only DeepHorn
`GeneralizedFlowCylinder.sliceHomeomorph` and the owned private
`cylinderSlice` in `ZeroSlice.lean`, without a zero-time clock cast.
Reviewed derivation: `claim11_35-fixed-time-cap-exclusion.md`, section 3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

/-- The actual included-time forward and inverse maps with their exact
exhaustion source and image target (Claims 11.34-11.35, pp. 288-290). -/
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

/-- Both literal included-time maps are smooth on their guarded domains
(Claims 11.34-11.35, printed pp. 288-290). -/
theorem blowup_sliceEmbedding_smooth (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) (t : ℝ) (htk : t ∈ Icc (-G.exhaustion.time k) 0) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (blowup_sliceEmbedding G k t htk)
        (G.exhaustion.space k) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (blowup_sliceEmbedding G k t htk).symm
        (blowup_sliceEmbedding G k t htk).target :=
  ⟨(G.embedding k).forward_smooth t htk, (G.embedding k).inverse_smooth t htk⟩

end PoincareMT.M32
