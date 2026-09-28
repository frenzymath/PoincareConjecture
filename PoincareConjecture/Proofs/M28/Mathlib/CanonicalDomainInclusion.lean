import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
  [Nonempty U] [Nonempty V]

theorem isLocalDiffeomorph_canonicalDomainInclusion :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ∞
      (fun x : U => (⟨x.val, hUV x.property⟩ : V)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro x
  let j : U → V := fun y => ⟨y.val, hUV y.property⟩
  have hi := isLocalDiffeomorph_subtypeVal 𝓘(𝕜, E) V hV ∞ (j x)
  have hx := isLocalDiffeomorph_subtypeVal 𝓘(𝕜, E) U hU ∞ x
  apply (hx.comp 𝓘(𝕜, E) V hi.localInverse_isLocalDiffeomorphAt).congr_of_eventuallyEq
  filter_upwards [hi.localInverse_eventuallyEq_right.comp_tendsto
    hx.contMDiffAt.continuousAt] with y hy
  apply Subtype.ext
  exact hy.symm

theorem mfderiv_canonicalDomainInclusion (x : U) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (fun y : U => (⟨y.val, hUV y.property⟩ : V)) x =
      ContinuousLinearMap.id 𝕜 E := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
  let j : U → V := fun y => ⟨y.val, hUV y.property⟩
  have hj := isLocalDiffeomorph_canonicalDomainInclusion (𝕜 := 𝕜) hU hV hUV x
  have hi := isLocalDiffeomorph_subtypeVal 𝓘(𝕜, E) V hV ∞ (j x)
  have hdU : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : U → E) x =
      ContinuousLinearMap.id 𝕜 E := mfderiv_extChartAt_self
  have hdV : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : V → E) (j x) =
      ContinuousLinearMap.id 𝕜 E := mfderiv_extChartAt_self
  ext z
  have hcomp := mfderiv_comp_apply x (hi.mdifferentiableAt (by simp))
    (hj.mdifferentiableAt (by simp)) z
  change mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : U → E) x z =
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : V → E) (j x)
      (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) j x z) at hcomp
  rw [hdU, hdV] at hcomp
  exact hcomp.symm

end Poincare
