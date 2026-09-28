import PoincareConjecture.Proofs.M14.Sec6_2_SurfaceTorsion
import PoincareConjecture.Proofs.M14.Mathlib.RectanglePartialTangent
import PoincareConjecture.Proofs.M14.Sec6_2_OpenFieldExtension

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {α : ℝ × ℝ → G.Point} {J P : Set ℝ}

theorem surfaceHorizontalFst_contMDiffOn (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (α z) (surfaceHorizontalFst α z.1 z.2)) (J ×ˢ P) := by
  have htan := hα.contMDiffOn_partialTangentWithin_fst_prod hJ.uniqueDiffOn hP.uniqueDiffOn
    (1 : ℝ) (k := ∞) (by simp)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  apply (hproj.comp_contMDiffOn htan).congr
  intro z hz
  simp only [Function.comp_apply, surfaceHorizontalFst,
    mfderivWithin_of_mem_nhds (hJ.mem_nhds hz.1)]

theorem surfaceHorizontalSnd_contMDiffOn (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (α z) (surfaceHorizontalSnd α z.1 z.2)) (J ×ˢ P) := by
  have htan := hα.contMDiffOn_partialTangent_snd_prod hJ.uniqueDiffOn hP
    (1 : ℝ) (k := ∞) (by simp)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  exact hproj.comp_contMDiffOn htan

theorem exists_surfaceHorizontalSnd_extension (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P))
    {v : ℝ} (hv : v ∈ P) :
    Nonempty (M14PullbackExtension G (fun s => α (s, v)) J
      (fun s => surfaceHorizontalSnd α s v)) := by
  apply exists_pullbackExtension_of_isOpen hJ
  exact (surfaceHorizontalSnd_contMDiffOn hJ hP hα).comp
    (contMDiff_id.prodMk (contMDiff_const (c := v))).contMDiffOn (fun _ hs => ⟨hs, hv⟩)

theorem exists_surfaceHorizontalFst_parameter_extension (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P))
    {s : ℝ} (hs : s ∈ J) :
    Nonempty (M14PullbackExtension G (fun v => α (s, v)) P
      (fun v => surfaceHorizontalFst α s v)) := by
  apply exists_pullbackExtension_of_isOpen hP
  exact (surfaceHorizontalFst_contMDiffOn hJ hP hα).comp
    ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn (fun _ hv => ⟨hs, hv⟩)

end PoincareConjecture.M14
