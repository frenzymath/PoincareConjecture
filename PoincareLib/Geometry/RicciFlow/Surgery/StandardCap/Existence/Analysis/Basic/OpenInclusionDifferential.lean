import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The differential of an open inclusion chart

In the singleton chart supplied by an open inclusion into a normed space,
the inclusion differential is the identity. This is the coordinate
identification used for the compact double in Morgan-Tian Theorem 12.5,
p. 297, compact-double derivation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

/-- An open subset's inclusion has identity derivative in its singleton
inclusion chart (Theorem 12.5, p. 297, compact-double derivation). -/
theorem mfderiv_subtypeVal_singleton
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {U : Set E} (hU : IsOpen U) [Nonempty U] (x : U) :
    let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : U → E) x =
      ContinuousLinearMap.id 𝕜 E := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
  change mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (extChartAt 𝓘(𝕜, E) x) x = _
  exact mfderiv_extChartAt_self
