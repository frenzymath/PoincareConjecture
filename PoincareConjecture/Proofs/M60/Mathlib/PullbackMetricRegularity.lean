import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M60




theorem continuousOn_pullback_inner
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle F (TangentSpace I : M → Type _)]
    {q : E → M} {S : Set E} (hS : IsOpen S) (hq : ContMDiffOn 𝓘(ℝ, E) I 1 q S) :
    ContinuousOn (fun p : E × (E × E) =>
      inner ℝ (mfderiv 𝓘(ℝ, E) I q p.1 p.2.1) (mfderiv 𝓘(ℝ, E) I q p.1 p.2.2))
      (S ×ˢ univ) := by
  have ht := hq.continuousOn_tangentMapWithin le_rfl hS.uniqueMDiffOn
  have hleft : ContinuousOn (fun p : E × (E × E) =>
      (⟨q p.1, mfderivWithin 𝓘(ℝ, E) I q S p.1 p.2.1⟩ : TangentBundle I M))
      (S ×ˢ univ) :=
    ht.comp (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp
      (continuous_fst.prodMk continuous_snd.fst)).continuousOn) (fun _ hp => hp.1)
  have hright : ContinuousOn (fun p : E × (E × E) =>
      (⟨q p.1, mfderivWithin 𝓘(ℝ, E) I q S p.1 p.2.2⟩ : TangentBundle I M))
      (S ×ˢ univ) :=
    ht.comp (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp
      (continuous_fst.prodMk continuous_snd.snd)).continuousOn) (fun _ hp => hp.1)
  apply (hleft.inner_bundle hright).congr
  intro p hp
  dsimp only
  erw [mfderivWithin_of_mem_nhds (hS.mem_nhds hp.1)]

end PoincareConjecture.M60
