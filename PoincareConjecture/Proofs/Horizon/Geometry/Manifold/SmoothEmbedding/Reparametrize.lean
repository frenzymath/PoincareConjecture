import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}
  [IsManifold 𝓘(𝕜, E) n M] {f g : M → N}

theorem IsImmersionOfComplement.comp_diffeomorph
    (hf : IsImmersionOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, G) n f)
    (e : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M n) :
    IsImmersionOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, G) n (f ∘ e) := by
  intro x
  let h := hf (e x)
  let d := e.toHomeomorph.toOpenPartialHomeomorph.trans h.domChart
  have hd : d ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M := by
    apply d.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        e.contMDiff.contMDiffOn (fun y hy => hy.2)
    · exact e.symm.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mono
          inter_subset_left)
  have hx : x ∈ d.source := ⟨mem_univ _, h.mem_domChart_source⟩
  have hsource (y : M) (hy : y ∈ d.source) : f (e y) ∈ h.codChart.source :=
    h.source_subset_preimage_source hy.2
  apply IsImmersionAtOfComplement.mk_of_charts h.equiv d h.codChart hx (hsource x hx)
    hd h.codChart_mem_maximalAtlas hsource
  intro v hv
  have hv' : v ∈ h.domChart.target := by
    have hvt : v ∈ d.target := by simpa using hv
    exact hvt.1
  change h.codChart (f (e (e.symm (h.domChart.symm v)))) = h.equiv (v, 0)
  rw [e.apply_symm_apply]
  exact h.writtenInCharts (by simpa using hv')

theorem IsSmoothEmbedding.comp_diffeomorph
    (hf : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, G) n f)
    (e : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M n) :
    IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, G) n (f ∘ e) :=
  ⟨(hf.isImmersion.isImmersionOfComplement_complement.comp_diffeomorph e).isImmersion,
    hf.isEmbedding.comp e.toHomeomorph.isEmbedding⟩

omit [IsManifold 𝓘(𝕜, E) n M] in

theorem IsSmoothEmbedding.exists_reparametrizing_diffeomorph
    (hf : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, G) n f)
    (hg : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, G) n g)
    (hrange : range f = range g) :
    ∃ e : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M n, ∀ x, g (e x) = f x := by
  let e : M ≃ₜ M := hf.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr hrange).trans hg.isEmbedding.toHomeomorph.symm)
  have heq (x : M) : g (e x) = f x := by
    have h := congrArg Subtype.val (hg.isEmbedding.toHomeomorph.apply_symm_apply
      ((Homeomorph.setCongr hrange) (hf.isEmbedding.toHomeomorph x)))
    exact h
  have hinv (x : M) : f (e.symm x) = g x := by
    rw [← heq (e.symm x), e.apply_symm_apply]
  have hsmooth : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n e := by
    apply (ContMDiff.iff_comp_isImmersion hg.isImmersion).mpr
    refine ⟨e.continuous, ?_⟩
    have he : g ∘ e = f := funext heq
    rw [he]
    exact hf.contMDiff
  have hinverse : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n e.symm := by
    apply (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr
    refine ⟨e.symm.continuous, ?_⟩
    have he : f ∘ e.symm = g := funext hinv
    rw [he]
    exact hg.contMDiff
  exact ⟨{ e.toEquiv with contMDiff_toFun := hsmooth, contMDiff_invFun := hinverse }, heq⟩

end Manifold
