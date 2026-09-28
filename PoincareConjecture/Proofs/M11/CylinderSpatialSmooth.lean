import PoincareConjecture.Proofs.M11.CylinderTangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {D : SmoothSpacetimeInterval K}
  {C : Type*} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C]

theorem cylinder_spatial_lift_smooth (D : SmoothSpacetimeInterval K) :
    ContMDiff ((𝓡∂ 1).prod ((𝓡 n).prod (𝓡 n)))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun q : D.Point × TangentBundle (𝓡 n) C ↦
        TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : D.Point × C → Type _))
          (q.1, q.2.proj) (0, q.2.2)) := by
  have ht : ContMDiff ((𝓡∂ 1).prod ((𝓡 n).prod (𝓡 n)))
      ((𝓡∂ 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
      (fun q : D.Point × TangentBundle (𝓡 n) C ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin 1))
          (E := (TangentSpace (𝓡∂ 1) : D.Point → Type _)) q.1 0) :=
    (contMDiff_zeroSection ℝ (TangentSpace (𝓡∂ 1) : D.Point → Type _)).comp contMDiff_fst
  exact contMDiff_equivTangentBundleProd_symm.comp (ht.prodMk contMDiff_snd)

noncomputable def cylinderSpatialTangentMap (e : CompatibleSpacetimeCylinder F D C)
    (q : D.Point × TangentBundle (𝓡 n) C) :
    TotalSpace (EuclideanSpace ℝ (Fin n)) F.Horizontal :=
  ⟨e.toSpacetime (q.1, q.2.proj), cylinderSpatialEquiv e q.1 q.2.proj q.2.2⟩

theorem cylinderSpatialTangentMap_smooth (e : CompatibleSpacetimeCylinder F D C) :
    ContMDiff ((𝓡∂ 1).prod ((𝓡 n).prod (𝓡 n)))
      ((spacetimeModel n).prod (𝓡 n)) ∞ (cylinderSpatialTangentMap e) := by
  let := F.chartedSpace
  let := F.isManifold
  let := F.horizontalTopology
  let := F.horizontalFiberBundle
  let := F.horizontalVectorBundle
  let := F.horizontalSmoothBundle
  have hpush := (e.smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (cylinder_spatial_lift_smooth (C := C) D)
  have hproj := F.horizontalProjection_smooth.comp hpush
  apply hproj.congr
  intro q
  apply TotalSpace.ext
  · rfl
  · apply heq_of_eq
    exact (F.horizontalProjection_identity _ (cylinderSpatialEquiv e q.1 q.2.proj q.2.2)).symm

end PoincareConjecture.Proofs.M11
