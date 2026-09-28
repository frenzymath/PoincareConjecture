import PoincareConjecture.Proofs.M11.BoxVector





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

theorem openSubtype_tangent_trivialization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : TopologicalSpace.Opens E) (x y : U) (v : E) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E) : U → Type _) x
      (TotalSpace.mk' E y v)).2 = v := by
  have hy : y ∈ (chartAt E x).source := ⟨trivial, mem_univ y.val⟩
  have hc := Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (trivializationAt E (TangentSpace 𝓘(ℝ, E) : U → Type _) x) hy
    (show TangentSpace 𝓘(ℝ, E) y from v)
  have hd := congrArg (fun L : E →L[ℝ] E ↦ L v)
    (TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℝ, E)) hy)
  have hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) y v = v := by
    rw [mfderiv_openSubtype_val]
    rfl
  exact hc.symm.trans (hd.trans hv)

theorem openSubtype_tangentLift_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : TopologicalSpace.Opens E) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p : U × E ↦ TotalSpace.mk' E (E := (TangentSpace 𝓘(ℝ, E) : U → Type _))
        p.1 p.2) := by
  intro p
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_fst, ?_⟩
  have heq : (fun q : U × E ↦
      (trivializationAt E (TangentSpace 𝓘(ℝ, E) : U → Type _) p.1
        (TotalSpace.mk' E q.1 q.2)).2) = Prod.snd := by
    funext q
    exact openSubtype_tangent_trivialization U p.1 q.1 q.2
  rw [heq]
  exact contMDiffAt_snd

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

theorem box_spatial_tangentLift_smooth (b : AdaptedMetricBox n X time I) :
    ContMDiff ((spacetimeModel n).prod (𝓡 n))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun p : boxDomain b × EuclideanSpace ℝ (Fin n) ↦
        TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : boxDomain b → Type _)) p.1 (0, p.2)) := by
  let := intervalChartedSpace b.interval
  let : IsManifold (𝓡∂ 1) ∞ b.interval.domain := interval_isManifold b.interval
  have ht : ContMDiff ((spacetimeModel n).prod (𝓡 n))
      ((𝓡∂ 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
      (fun p : boxDomain b × EuclideanSpace ℝ (Fin n) ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin 1))
          (E := (TangentSpace (𝓡∂ 1) : b.interval.domain → Type _)) p.1.1 0) :=
    (contMDiff_zeroSection ℝ (TangentSpace (𝓡∂ 1) : b.interval.domain → Type _)).comp
      (contMDiff_fst.comp contMDiff_fst)
  have hx : ContMDiff ((spacetimeModel n).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p : boxDomain b × EuclideanSpace ℝ (Fin n) ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := (TangentSpace (𝓡 n) : b.spatial → Type _)) p.1.2 p.2) :=
    (openSubtype_tangentLift_smooth b.spatial).comp
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  exact contMDiff_equivTangentBundleProd_symm.comp (ht.prodMk hx)

theorem box_spatial_push_smooth (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    letI := intervalChartedSpace (A.box b).interval
    letI := adaptedChartedSpace A
    letI : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
    ContMDiff ((spacetimeModel n).prod (𝓡 n))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun p : boxDomain (A.box b) × EuclideanSpace ℝ (Fin n) ↦
        TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : X → Type _)) ((A.box b).toSpacetime p.1)
          (mfderiv (spacetimeModel n) (spacetimeModel n) (A.box b).toSpacetime p.1 (0, p.2))) := by
  let := intervalChartedSpace (A.box b).interval
  let : IsManifold (𝓡∂ 1) ∞ (A.box b).interval.domain := interval_isManifold (A.box b).interval
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  exact ((adapted_box_localDiffeomorph A b).contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (box_spatial_tangentLift_smooth (A.box b))

end PoincareConjecture.Proofs.M11
