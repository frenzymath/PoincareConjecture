import PoincareConjecture.Definitions.M11GeneralizedFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

structure HorizontalBundleData (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X]
    [IsManifold (spacetimeModel n) ∞ X]
    (K : X → Submodule ℝ (SpacetimeModelVector n)) where
  topology : TopologicalSpace
    (Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ K p))
  fiberBundle : FiberBundle (EuclideanSpace ℝ (Fin n)) (fun p ↦ K p)
  vectorBundle : VectorBundle ℝ (EuclideanSpace ℝ (Fin n)) (fun p ↦ K p)
  smoothBundle : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin n))
    (fun p ↦ K p) (spacetimeModel n)
  inclusion_smooth :
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ K p) ↦
        Bundle.TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : X → Type _)) v.proj v.2.val)
  projection : ∀ p : X, TangentSpace (spacetimeModel n) p →L[ℝ] K p
  projection_identity : ∀ p (v : K p), projection p v.val = v
  projection_smooth :
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) X ↦
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := fun p ↦ K p) v.proj (projection v.proj v.2))
  metric : Bundle.ContMDiffRiemannianMetric (spacetimeModel n) ∞
    (EuclideanSpace ℝ (Fin n)) (fun p ↦ K p)

namespace HorizontalBundleData

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X]
  [IsManifold (spacetimeModel n) ∞ X]
  {K L : X → Submodule ℝ (SpacetimeModelVector n)}

noncomputable def transport (D : HorizontalBundleData n X K) (h : K = L) :
    HorizontalBundleData n X L := h ▸ D

noncomputable def fiberEquiv (h : K = L) (p : X) : K p ≃L[ℝ] L p :=
  ContinuousLinearEquiv.ofEq (K p) (L p) (congrFun h p)

omit [TopologicalSpace X]
  [ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X]
  [IsManifold (spacetimeModel n) ∞ X] in
theorem fiberEquiv_val (h : K = L) (p : X) (v : K p) :
    (fiberEquiv h p v).val = v.val := rfl

theorem transport_projection (D : HorizontalBundleData n X K) (h : K = L)
    (p : X) (Z : TangentSpace (spacetimeModel n) p) :
    (D.transport h).projection p Z = fiberEquiv h p (D.projection p Z) := by
  subst L
  rfl

theorem transport_projection_val (D : HorizontalBundleData n X K) (h : K = L)
    (p : X) (Z : TangentSpace (spacetimeModel n) p) :
    ((D.transport h).projection p Z).val = (D.projection p Z).val := by
  rw [transport_projection, fiberEquiv_val]

theorem transport_metric (D : HorizontalBundleData n X K) (h : K = L)
    (p : X) (v w : K p) :
    letI := D.topology
    letI := D.fiberBundle
    letI := D.vectorBundle
    letI := (D.transport h).topology
    letI := (D.transport h).fiberBundle
    letI := (D.transport h).vectorBundle
    (D.transport h).metric.inner p (fiberEquiv h p v) (fiberEquiv h p w) =
      D.metric.inner p v w := by
  subst L
  rfl

theorem transport_smooth (D : HorizontalBundleData n X K) (h : K = L) :
    letI := D.topology
    letI := D.fiberBundle
    letI := (D.transport h).topology
    letI := (D.transport h).fiberBundle
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ K p) ↦
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := fun p ↦ L p) v.proj (fiberEquiv h v.proj v.2)) := by
  subst L
  let := D.topology
  let := D.fiberBundle
  change ContMDiff _ _ ∞ id
  exact contMDiff_id

theorem transport_inverse_smooth (D : HorizontalBundleData n X K) (h : K = L) :
    letI := D.topology
    letI := D.fiberBundle
    letI := (D.transport h).topology
    letI := (D.transport h).fiberBundle
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ L p) ↦
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := fun p ↦ K p) v.proj ((fiberEquiv h v.proj).symm v.2)) := by
  subst L
  let := D.topology
  let := D.fiberBundle
  change ContMDiff _ _ ∞ id
  exact contMDiff_id

end HorizontalBundleData

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

noncomputable def spacetimeHorizontalBundle (S : GeneralizedFlowSpacetime n X time I) :
    HorizontalBundleData n S.Point
      (fun p ↦ spacetimeHorizontal (n := n) S.timeFunction p) where
  topology := S.horizontalTopology
  fiberBundle := S.horizontalFiberBundle
  vectorBundle := S.horizontalVectorBundle
  smoothBundle := S.horizontalSmoothBundle
  inclusion_smooth := S.horizontal_inclusion_smooth
  projection := S.horizontalProjection
  projection_identity := S.horizontalProjection_identity
  projection_smooth := S.horizontalProjection_smooth
  metric := S.metric

end PoincareConjecture.M13
