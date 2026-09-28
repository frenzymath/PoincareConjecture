import PoincareConjecture.Proofs.M34.Mathlib.OpenDomainCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V) [Nonempty U] [Nonempty V]

omit [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nonempty U] in

theorem canonicalOpen_map_coe (f : E → F) :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ (p : V) (x : U), f x ∈ V →
      (((extChartAt 𝓘(𝕜, F) p).symm (f x) : V) : F) = f x := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p x hx
  simpa only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm,
    Function.comp_apply, id_eq] using canonicalOpen_chart_coe_symm hV p (f x) hx

theorem canonicalOpen_map_contMDiffAt {f : E → F} {x : U}
    (hf : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) ∞ f (x : E)) (hx : f x ∈ V) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, F)) (n := ∞)
    ∀ p : V, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) ∞
      (fun y : U => (extChartAt 𝓘(𝕜, F) p).symm (f y)) x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, F)) (n := ∞)
  intro p
  have hi : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ∞ (Subtype.val : U → E) x :=
    (contMDiff_isOpenEmbedding (I := 𝓘(𝕜, E)) (n := ∞)
      hU.isOpenEmbedding_subtypeVal).contMDiffAt
  exact (canonicalOpen_contMDiffAt_symm hV p (f x) hx).comp x (hf.comp x hi)

theorem canonicalOpen_map_mfderiv {f : E → F} {x : U}
    (hf : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f (x : E)) (hx : f x ∈ V) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, F)) (n := ∞)
    ∀ p : V, mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F)
      (fun y : U => (extChartAt 𝓘(𝕜, F) p).symm (f y)) x =
        mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f (x : E) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, F)) (n := ∞)
  intro p
  have hi : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : U → E) x :=
    (contMDiff_isOpenEmbedding (I := 𝓘(𝕜, E)) (n := ∞)
      hU.isOpenEmbedding_subtypeVal).mdifferentiable (by simp) x
  have hr := (canonicalOpen_contMDiffAt_symm (𝕜 := 𝕜) hV p (f x) hx).mdifferentiableAt
    (by simp)
  have hh := mfderiv_comp x hr (hf.comp x hi)
  erw [canonicalOpen_mfderiv_symm (𝕜 := 𝕜) hV p (f x) hx,
    canonicalOpen_mfderiv_restrict hU 𝓘(𝕜, F) hf] at hh
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L => L v) hh
