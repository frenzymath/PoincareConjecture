import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.GeneralizedLimit.GeneralizedSpatialSlices
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Literal terminal maps for a retained generalized cylinder

Normalize the zero-time target once, together with its source and point
identity, before pulling back a buffered source flow. This keeps all
subsequent maps on the actual terminal slice.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

/-- The terminal spatial cylinder is an actual partial diffeomorphism
into the unshifted source slice, with its literal point identity. -/
theorem exists_generalized_terminal_partialDiffeomorph
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) :
    ∃ d : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.carrier.carrier
        ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier ∞,
      d.source = G.exhaustion.space k ∧
        ∀ (h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0) (x : G.limit.carrier.carrier),
          (G.embedding k).pointMap 0 h0 x =
            Sigma.mk (S.base (G.subsequence k)).1 (d x) := by
  have hzero : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  let e := generalizedSliceHomeomorph G k 0 hzero
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.carrier.carrier
      ((S.flow (G.subsequence k)).slice
        ((S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k))).carrier ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := fun x hx =>
      (generalizedSliceHomeomorph_contMDiffAt G k 0 hzero hx).contMDiffWithinAt
    contMDiffOn_invFun := fun y hy =>
      (generalizedSliceHomeomorph_symm_contMDiffAt G k 0 hzero hy).contMDiffWithinAt }
  have h : ∃ d' : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.carrier.carrier
      ((S.flow (G.subsequence k)).slice
        ((S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k))).carrier ∞,
      d'.source = G.exhaustion.space k ∧
        ∀ (h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0) (x : G.limit.carrier.carrier),
          (G.embedding k).pointMap 0 h0 x =
            Sigma.mk ((S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k))
              (d' x) := by
    exact ⟨d, rfl, fun _ _ => rfl⟩
  rw [show (S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k) =
    (S.base (G.subsequence k)).1 by simp] at h
  exact h

end PoincareMT.M30
