import PoincareLib.Geometry.Manifold.SmoothEmbedding.Slice

/-!
# Smooth graphs in open product coordinates

A smooth shear reduces a graph to the zero slice of a smooth open partial
homeomorphism. This is the graph-embedding step in Morgan--Tian
Proposition A.11, pp. 503-504, and Lemma A.13, p. 505.

Adapted from Mapher, `PoincareMT/Proofs/M25/Mathlib/SmoothGraph.lean`,
commit `56d9cc710a322b1e69daa9353c1758b861c0e3fe`.
-/

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

/-- A smooth graph contained in smooth product coordinates is a smooth
embedding. -/
theorem isSmoothEmbedding_graph (e : OpenPartialHomeomorph (M × F) N)
    (he : ContMDiffOn (𝓘(𝕜, E).prod 𝓘(𝕜, F)) 𝓘(𝕜, G) n e e.source)
    (hi : ContMDiffOn 𝓘(𝕜, G) (𝓘(𝕜, E).prod 𝓘(𝕜, F)) n e.symm e.target)
    (L : (E × F) ≃L[𝕜] G) (f : M → F)
    (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n f)
    (hsource : ∀ x : M, (x, f x) ∈ e.source) :
    Manifold.IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, G) n (fun x => e (x, f x)) := by
  let h : (M × F) ≃ₜ (M × F) :=
    { toFun := fun z => (z.1, z.2 + f z.1)
      invFun := fun z => (z.1, z.2 - f z.1)
      left_inv := fun z => by simp
      right_inv := fun z => by simp
      continuous_toFun := continuous_fst.prodMk
        (continuous_snd.add (hf.continuous.comp continuous_fst))
      continuous_invFun := continuous_fst.prodMk
        (continuous_snd.sub (hf.continuous.comp continuous_fst)) }
  have hh : ContMDiff (𝓘(𝕜, E).prod 𝓘(𝕜, F))
      (𝓘(𝕜, E).prod 𝓘(𝕜, F)) n h :=
    contMDiff_fst.prodMk (contDiff_add.contMDiff.comp
      (contMDiff_snd.prodMk_space (hf.comp contMDiff_fst)))
  have hh' : ContMDiff (𝓘(𝕜, E).prod 𝓘(𝕜, F))
      (𝓘(𝕜, E).prod 𝓘(𝕜, F)) n h.symm :=
    contMDiff_fst.prodMk ((contDiff_fst.sub contDiff_snd).contMDiff.comp
      (contMDiff_snd.prodMk_space (hf.comp contMDiff_fst)))
  let d := h.toOpenPartialHomeomorph.trans e
  have hd : ContMDiffOn (𝓘(𝕜, E).prod 𝓘(𝕜, F)) 𝓘(𝕜, G) n d d.source :=
    he.comp hh.contMDiffOn (fun z hz => hz.2)
  have hd' : ContMDiffOn 𝓘(𝕜, G) (𝓘(𝕜, E).prod 𝓘(𝕜, F)) n d.symm d.target :=
    hh'.comp_contMDiffOn (hi.mono (fun z hz => hz.1))
  have hzero (x : M) : (x, (0 : F)) ∈ d.source := by
    refine ⟨mem_univ _, ?_⟩
    change (x, 0 + f x) ∈ e.source
    simpa only [zero_add] using hsource x
  have hslice := d.isSmoothEmbedding_slice hd hd' L 0 hzero
  change Manifold.IsSmoothEmbedding _ _ n (fun x => e (x, 0 + f x)) at hslice
  simpa only [zero_add] using hslice

end OpenPartialHomeomorph
