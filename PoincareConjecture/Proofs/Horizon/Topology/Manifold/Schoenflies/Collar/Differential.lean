import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Sphere









set_option autoImplicit false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace Manifold.IsImmersionAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} {f : M → N} {x : M}



theorem injective_mfderiv_modelWithCornersSelf
    (h : IsImmersionAt 𝓘(𝕜, E) J n f x) (hn : n ≠ 0) :
    Injective (mfderiv 𝓘(𝕜, E) J f x) := by
  let p : E' →L[𝕜] E :=
    (ContinuousLinearMap.fst 𝕜 E h.complement).comp h.equiv.symm.toContinuousLinearMap
  let g : N → M := h.domChart.symm ∘ p ∘ (h.codChart.extend J)
  have hleft : g ∘ f =ᶠ[𝓝 x] id := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hy' : y ∈ (h.domChart.extend 𝓘(𝕜, E)).source := by simpa using hy
    have hcoords : (h.codChart.extend J) (f y) = h.equiv (h.domChart y, 0) := by
      have hw := h.writtenInCharts ((h.domChart.extend 𝓘(𝕜, E)).map_source hy')
      simp only [Function.comp_apply, (h.domChart.extend 𝓘(𝕜, E)).left_inv hy'] at hw
      simpa only [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
        Function.comp_apply, id_eq] using hw
    change h.domChart.symm (p ((h.codChart.extend J) (f y))) = y
    rw [hcoords]
    simpa [p] using h.domChart.left_inv hy
  have hpx : p ((h.codChart.extend J) (f x)) = h.domChart x := by
    have hx' : x ∈ (h.domChart.extend 𝓘(𝕜, E)).source := by
      simpa using h.mem_domChart_source
    have hw := h.writtenInCharts
      ((h.domChart.extend 𝓘(𝕜, E)).map_source hx')
    have hcoords : (h.codChart.extend J) (f x) = h.equiv (h.domChart x, 0) := by
      simp only [Function.comp_apply,
        (h.domChart.extend 𝓘(𝕜, E)).left_inv hx'] at hw
      simpa only [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
        Function.comp_apply, id_eq] using hw
    rw [hcoords]
    simp [p]
  have hg : ContMDiffAt J 𝓘(𝕜, E) n g (f x) := by
    have hd := contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      (h.domChart.map_source h.mem_domChart_source)
    rw [← hpx] at hd
    exact hd.comp (f x) (p.contMDiff.contMDiffAt.comp (f x)
      (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas h.mem_codChart_source))
  have hderiv := hleft.mfderiv_eq (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, E))
  rw [mfderiv_comp _ (hg.mdifferentiableAt hn) (h.contMDiffAt.mdifferentiableAt hn),
    mfderiv_id] at hderiv
  intro u v huv
  have heq := congrArg (mfderiv J 𝓘(𝕜, E) g (f x)) huv
  simp only [← ContinuousLinearMap.comp_apply, hderiv] at heq
  exact heq

end Manifold.IsImmersionAt

namespace Poincare.Manifold.Schoenflies

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1


theorem injective_mfderiv_sphere_embedding {f : S2 → E3}
    (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) (p : S2) :
    Injective (mfderiv (𝓡 2) (𝓡 3) f p) :=
  (hf.isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf (by simp)



theorem injOn_fderiv_extension_tangent_sphere {f : S2 → E3}
    (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {G : E3 → E3} (hG : ContDiff ℝ ∞ G)
    (hrestrict : ∀ p : S2, G p = f p) (p : S2) :
    InjOn (fderiv ℝ G p) {v : E3 | inner ℝ (p : E3) v = 0} := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  let L : TangentSpace (𝓡 2) p →L[ℝ] E3 :=
    mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) p
  have hrange : L.range = (ℝ ∙ (p : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have hchain : mfderiv (𝓡 2) (𝓡 3) f p = (fderiv ℝ G p).comp L := by
    have heq : f = G ∘ (Subtype.val : S2 → E3) := funext fun y => (hrestrict y).symm
    rw [heq, mfderiv_comp _ (hG.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_coe_sphere (n := 2) p).mdifferentiableAt
        (show (∞ : ℕ∞ω) ≠ 0 by simp)),
      mfderiv_eq_fderiv]
    rfl
  intro u hu v hv huv
  have hu' : u ∈ L.range := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hu
  have hv' : v ∈ L.range := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hv
  obtain ⟨u', rfl⟩ := hu'
  obtain ⟨v', rfl⟩ := hv'
  apply congrArg L
  apply injective_mfderiv_sphere_embedding hf p
  rw [hchain]
  exact huv

end Poincare.Manifold.Schoenflies
