import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E G F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω} [IsManifold 𝓘(𝕜, G) n P]
  {f : M → N} {p : N → P}


theorem IsImmersionOfComplement.comp_localDiffeomorph
    (hf : IsImmersionOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, G) n f)
    (hp : IsLocalDiffeomorph 𝓘(𝕜, G) 𝓘(𝕜, G) n p) :
    IsImmersionOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, G) n (p ∘ f) := by
  intro x
  let h := hf x
  obtain ⟨φ, hx, heq⟩ := hp (f x)
  let s := f ⁻¹' φ.source
  have hs : IsOpen s := φ.open_source.preimage hf.contMDiff.continuous
  let d := h.domChart.restr s
  let b := φ.symm.toOpenPartialHomeomorph.trans h.codChart
  have hdsource : d.source = h.domChart.source ∩ s :=
    h.domChart.restr_source' s hs
  have hb : b ∈ IsManifold.maximalAtlas 𝓘(𝕜, G) n P := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        (φ.symm.contMDiffOn.mono inter_subset_left) inter_subset_right
    · exact φ.contMDiffOn.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          inter_subset_left) inter_subset_right
  have hsource (y : M) (hy : y ∈ d.source) : p (f y) ∈ b.source := by
    rw [hdsource] at hy
    have hfy : f y ∈ φ.source := hy.2
    change p (f y) ∈ φ.target ∧ φ.symm (p (f y)) ∈ h.codChart.source
    rw [heq hfy]
    change φ (f y) ∈ φ.target ∧ φ.toPartialEquiv.symm (φ.toPartialEquiv (f y)) ∈ _
    rw [φ.toPartialEquiv.left_inv hfy]
    exact ⟨φ.map_source hfy, h.source_subset_preimage_source hy.1⟩
  have hdx : x ∈ d.source := by rw [hdsource]; exact ⟨h.mem_domChart_source, hx⟩
  apply IsImmersionAtOfComplement.mk_of_charts h.equiv d b hdx (hsource x hdx)
    (restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas hs) hb hsource
  intro v hv
  have hv' : v ∈ d.target := by simpa using hv
  have hdv := d.map_target hv'
  rw [hdsource] at hdv
  have hfv : f (d.symm v) ∈ φ.source := hdv.2
  change h.codChart (φ.symm (p (f (d.symm v)))) = h.equiv (v, 0)
  rw [heq hfv]
  change h.codChart (φ.toPartialEquiv.symm (φ.toPartialEquiv (f (d.symm v)))) = _
  rw [φ.toPartialEquiv.left_inv hfv]
  apply h.writtenInCharts
  simpa using hv'.1


theorem IsImmersion.comp_localDiffeomorph
    (hf : IsImmersion 𝓘(𝕜, E) 𝓘(𝕜, G) n f)
    (hp : IsLocalDiffeomorph 𝓘(𝕜, G) 𝓘(𝕜, G) n p) :
    IsImmersion 𝓘(𝕜, E) 𝓘(𝕜, G) n (p ∘ f) :=
  (hf.isImmersionOfComplement_complement.comp_localDiffeomorph hp).isImmersion



theorem IsSmoothEmbedding.comp_localDiffeomorph [CompactSpace M] [T2Space P]
    (hf : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, G) n f)
    (hp : IsLocalDiffeomorph 𝓘(𝕜, G) 𝓘(𝕜, G) n p)
    (hinj : Function.Injective (p ∘ f)) :
    IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, G) n (p ∘ f) := by
  have hi := hf.isImmersion.comp_localDiffeomorph hp
  exact ⟨hi, (hi.contMDiff.continuous.isClosedEmbedding hinj).isEmbedding⟩

end Manifold
