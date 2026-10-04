import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.OpenSubsetTransition
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Smooth transitions restricted to an open model subset

Conjugating a smooth transition by the inclusion chart preserves
smoothness on its exact source. This is the manifold restriction in
Morgan-Tian Theorem 12.5, p. 297, compact-double derivation.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (e : OpenPartialHomeomorph H H) {U : Set H} (hU : IsOpen U) [Nonempty U]
  {n : ℕ∞ω}

/-- Smoothness survives restriction of both source and target to an open
subset of the model (Theorem 12.5, p. 297, compact-double derivation). -/
theorem contMDiffOn_onOpenSubset (he : ContMDiffOn I I n e e.source)
    (htarget : e.target ⊆ U) :
    let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiffOn I I n (e.onOpenSubset hU) (e.onOpenSubset hU).source := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  rw [onOpenSubset_source e hU htarget]
  have hc : ContMDiff I I n (Subtype.val : U → H) :=
    contMDiff_isOpenEmbedding (I := I) hU.isOpenEmbedding_subtypeVal
  have hi := contMDiffOn_isOpenEmbedding_symm (I := I) (n := n)
    hU.isOpenEmbedding_subtypeVal
  have hcomp := he.comp hc.contMDiffOn (fun _ hx => hx)
  have hresult := hi.comp hcomp (fun x hx =>
    (show e (x : H) ∈ range (Subtype.val : U → H) from
      ⟨⟨e (x : H), htarget (e.map_source hx)⟩, rfl⟩))
  simpa only [onOpenSubset, coe_trans,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply] using hresult

end OpenPartialHomeomorph
