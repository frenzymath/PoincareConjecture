import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}
  [IsManifold 𝓘(𝕜, E) n M] [IsManifold 𝓘(𝕜, G) n N]

theorem m25_isSmoothEmbedding_slice (e : OpenPartialHomeomorph (M × F) N)
    (he : ContMDiffOn (𝓘(𝕜, E).prod 𝓘(𝕜, F)) 𝓘(𝕜, G) n e e.source)
    (hi : ContMDiffOn 𝓘(𝕜, G) (𝓘(𝕜, E).prod 𝓘(𝕜, F)) n e.symm e.target)
    (L : (E × F) ≃L[𝕜] G) (c : F) (hc : ∀ x : M, (x, c) ∈ e.source) :
    Manifold.IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, G) n (fun x => e (x, c)) := by
  refine ⟨?_, e.isEmbedding_restrict.comp
    ((isEmbedding_prodMkLeft c).codRestrict e.source hc)⟩
  apply Manifold.IsImmersionOfComplement.isImmersion (F := F)
  intro x
  let d := chartAt E x
  let p := d.prod (Homeomorph.addRight (-c)).toOpenPartialHomeomorph
  let b := (e.symm.trans p).trans L.toHomeomorph.toOpenPartialHomeomorph
  have hp : ContMDiffOn (𝓘(𝕜, E).prod 𝓘(𝕜, F)) 𝓘(𝕜, E × F) n p p.source := by
    have hshift : ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, F) n (fun y : F => y + -c) :=
      (contDiff_id.add contDiff_const).contMDiff
    exact ((contMDiffOn_chart (I := 𝓘(𝕜, E)) (x := x)).comp
      contMDiffOn_fst (fun y hy => hy.1)).prodMk_space
        (hshift.comp_contMDiffOn contMDiffOn_snd)
  have hp' : ContMDiffOn 𝓘(𝕜, E × F) (𝓘(𝕜, E).prod 𝓘(𝕜, F)) n
      p.symm p.target := by
    have hshift : ContMDiff 𝓘(𝕜, E × F) 𝓘(𝕜, F) n
        (fun y : E × F => y.2 + -(-c)) :=
      (contDiff_snd.add contDiff_const).contMDiff
    exact ((contMDiffOn_chart_symm (I := 𝓘(𝕜, E)) (x := x)).comp
      contDiff_fst.contMDiff.contMDiffOn (fun y hy => hy.1)).prodMk hshift.contMDiffOn
  have hb : b ∈ IsManifold.maximalAtlas 𝓘(𝕜, G) n N := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn 𝓘(𝕜, G) 𝓘(𝕜, G) n (L ∘ p ∘ e.symm) b.source
      apply L.contDiff.contMDiff.comp_contMDiffOn
      exact hp.comp (hi.mono (fun y hy => hy.1.1)) (fun y hy => hy.1.2)
    · change ContMDiffOn 𝓘(𝕜, G) 𝓘(𝕜, G) n (e ∘ p.symm ∘ L.symm) b.target
      exact he.comp
        (hp'.comp L.symm.contDiff.contMDiff.contMDiffOn (fun y hy => hy.2.1))
        (fun y hy => hy.2.2)
  have hsource (y : M) (hy : y ∈ d.source) : e (y, c) ∈ b.source := by
    refine ⟨⟨e.map_source (hc y), ?_⟩, Set.mem_univ _⟩
    change e.symm (e (y, c)) ∈ p.source
    rw [e.left_inv (hc y)]
    exact ⟨hy, Set.mem_univ _⟩
  apply Manifold.IsImmersionAtOfComplement.mk_of_charts L d b
    (mem_chart_source E x) (hsource x (mem_chart_source E x))
    (IsManifold.chart_mem_maximalAtlas x) hb hsource
  intro v hv
  have hv' : v ∈ d.target := by simpa using hv
  change L (p (e.symm (e (d.symm v, c)))) = L (v, 0)
  rw [e.left_inv (hc _)]
  congr 1
  change (d (d.symm v), c + -c) = (v, 0)
  rw [d.right_inv hv', add_neg_cancel]

end OpenPartialHomeomorph
