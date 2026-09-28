import PoincareConjecture.Proofs.M32.Claim11_34.ZeroSlice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem blowup_zeroSliceEmbedding_pointMap
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ)
    (hzero : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0)
    (x : G.limit.carrier.carrier) :
    (G.embedding k).pointMap 0 hzero x =
      (⟨(S.base (G.subsequence k)).1, blowup_zeroSliceEmbedding G k x⟩ :
        (S.flow (G.subsequence k)).point) := by
  have hcast {F : GeneralizedRicciFlowData.{u}} {C : Type u}
      [TopologicalSpace C] {a b : ℝ}
      (e : OpenPartialHomeomorph C (F.slice a).carrier) (h : a = b) (z : C) :
      (⟨a, e z⟩ : F.point) = ⟨b, (h ▸ e) z⟩ := by
    cases h
    rfl
  let e : OpenPartialHomeomorph G.limit.sliceCarrier.carrier
      ((S.flow (G.subsequence k)).slice
        ((S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k))).carrier := {
    toFun := (G.embedding k).forward 0 hzero
    invFun := (G.embedding k).inverse 0 hzero
    source := G.exhaustion.space k
    target := (G.embedding k).forward 0 hzero '' G.exhaustion.space k
    map_source' := fun z hz => mem_image_of_mem _ hz
    map_target' := by
      rintro z ⟨y, hy, rfl⟩
      rw [(G.embedding k).left_inverse 0 hzero hy]
      exact hy
    left_inv' := (G.embedding k).left_inverse 0 hzero
    right_inv' := (G.embedding k).right_inverse 0 hzero
    open_source := G.exhaustion.space_open k
    open_target := cylinder_isOpen_forward_image (G.embedding k)
      (G.exhaustion.space_open k) 0 hzero
    continuousOn_toFun := ((G.embedding k).forward_smooth 0 hzero).continuousOn
    continuousOn_invFun := ((G.embedding k).inverse_smooth 0 hzero).continuousOn }
  exact hcast e (by simp) x

end PoincareConjecture.M32
