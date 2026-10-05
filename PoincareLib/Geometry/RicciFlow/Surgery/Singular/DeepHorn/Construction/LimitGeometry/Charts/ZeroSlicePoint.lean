import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.LimitGeometry.Charts.ZeroSlice

/-!
# The literal spacetime point of the terminal embedding

Morgan--Tian Claim 11.35, printed pp. 289-291. Equality at zero anchors
the comparison of actual source cylinder trajectories. This rederives
the private cylinderSliceAt_pointMap calculation in ZeroSlice and the
same reviewed clock calculation in Continuation/SeedScalar.
Reviewed derivation: `claim11_35-stage-controls-and-limit-bound.md`, section 3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

/-- The actual zero-time cylinder point is the same original base-slice
point under the retained terminal embedding; Claim 11.35, pp. 289-291. -/
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

end PoincareMT.M32
