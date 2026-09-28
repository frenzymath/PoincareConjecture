import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def parametricExtensionInChart
    {I U : Set ℝ} {γ : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (γ s)}
    (e : Bundle.Trivialization (EuclideanSpace ℝ (Fin n))
      (Bundle.TotalSpace.proj : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) → M))
    [MemTrivializationAtlas e]
    (y : ℝ → EuclideanSpace ℝ (Fin n)) (hU : IsOpen U) (hIU : I ⊆ U)
    (hγ : ∀ s ∈ I, γ s ∈ e.baseSet)
    (hy : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ y U)
    (hY : ∀ s ∈ I, e.symm (γ s) (y s) = Y s) :
    ParametricAlongCurveExtensionOn I γ Y where
  extension s x := e.symm x (y s)
  domain := U ×ˢ e.baseSet
  open_domain := hU.prod e.open_baseSet
  graph_mem s hs := ⟨hIU hs, hγ s hs⟩
  smooth := by
    have hmap : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun z : ℝ × M ↦ (z.2, y z.1)) (U ×ˢ e.baseSet) :=
      contMDiffOn_snd.prodMk (hy.comp contMDiffOn_fst (fun _ hz ↦ hz.1))
    exact (e.contMDiffOn_symm.comp hmap
      (fun _ hz ↦ e.mem_target.mpr hz.2)).congr
        (fun z hz ↦ e.mk_symm hz.2 (y z.1))
  agrees := hY

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
