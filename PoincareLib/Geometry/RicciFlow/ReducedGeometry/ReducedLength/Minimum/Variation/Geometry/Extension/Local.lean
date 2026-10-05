import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic

/-!
# Parametric field extensions in a tangent-bundle chart

Adapted from Mapher `Proofs/M08/ChartExtensions.lean`, commit
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.

A smooth coordinate field extends off the graph by keeping its coordinates
constant in the spatial variable of one tangent-bundle trivialization.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- A smooth coefficient curve gives an actual extension on one bundle-chart product. -/
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

end PoincareMT.ReducedLengthMinimum.Variation.Geometry
