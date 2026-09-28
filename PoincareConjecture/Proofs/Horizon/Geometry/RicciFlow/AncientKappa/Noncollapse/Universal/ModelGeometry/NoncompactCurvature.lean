import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Transport.Canonical
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Models
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

private theorem cylinder_sphere_scalar (t : ℝ) (ht : t < 0) (x : UnitTwoSphere) :
    (RicciFlow.Splitting.RoundCylinderSurface.sphereConnection t).scalarCurvature x =
      -1 / t := by
  have hround : (roundSphereMetric 2).leviCivitaData.scalarCurvature x = 2 := by
    have h := (roundSphereMetric 2).leviCivitaData.scalarCurvature_of_constant_sectional
      x 1 (roundSphereMetric_unit_sectionalCurvature x)
    norm_num at h ⊢
    exact h
  rw [RicciFlow.Splitting.RoundCylinderSurface.sphereConnection,
    rescaledMetric_scalarCurvature, hround,
    RicciFlow.Splitting.RoundCylinderSurface.scale, if_pos ht]
  field_simp

namespace SphereLineProductData

variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]
  (B : SphereLineProductData (P := P))

local instance curvatureSurfaceTopology : TopologicalSpace B.surface := B.surface_topology
local instance curvatureSurfaceChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) B.surface := B.surface_charted
local instance curvatureSurfaceManifold : IsManifold (𝓡 2) ∞ B.surface := B.surface_manifold
local instance curvatureProductChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (B.surface × ℝ) := B.product_charted
local instance curvatureProductManifold : IsManifold (𝓡 3) ∞ (B.surface × ℝ) :=
  B.product_manifold

theorem product_scalarCurvature (t : ℝ) (ht : t < 0) (p : B.surface × ℝ) :
    (B.product_connection t).scalarCurvature p = -1 / t := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 1))) (B.surface × ℝ) := B.product_charted
  let : IsManifold (𝓡 (2 + 1)) ∞ (B.surface × ℝ) := B.product_manifold
  let g := RicciFlow.Splitting.RoundCylinderSurface.sphereMetric t
  let D := RicciFlow.Splitting.RoundCylinderSurface.sphereConnection t
  let e := B.canonicalProductDiffeomorph
  have hmetric (z : UnitTwoSphere × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      (B.product_metric t).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
        g.inner z.1 v.1 w.1 + v.2 * w.2 := by
    rw [B.canonicalProductDiffeomorph_inner t ht]
    change _ = (rescaledMetric (roundSphereMetric 2)
      (RicciFlow.Splitting.RoundCylinderSurface.scale t)
      (RicciFlow.Splitting.RoundCylinderSurface.scale_pos t)).inner z.1 v.1 w.1 + _
    rw [rescaledMetric_inner, RicciFlow.Splitting.RoundCylinderSurface.scale, if_pos ht,
      roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner]
  have h := g.scalarCurvature_eq_of_line_product (B.product_metric t) D
    (B.product_connection t) e hmetric (e.symm p)
  rw [e.apply_symm_apply] at h
  exact h.trans (cylinder_sphere_scalar t ht (e.symm p).1)

end SphereLineProductData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}

theorem SphereLineProductCertificate.scalarCurvature
    (C : SphereLineProductCertificate G) (t : ℝ) (ht : t < 0) (p : M) :
    (G.flow.connection t).scalarCurvature p = -1 / t := by
  let := C.surface_topology
  let := C.product_charted
  let := C.product_manifold
  have h := (G.flow.connection t).scalarCurvature_eq_of_local_isometry
    (C.product_connection t) isOpen_univ C.product_equiv.contMDiff.contMDiffOn
    (fun x _ => C.flow_isometric_to_product t ht x) (mem_univ p)
  exact h.trans (C.toSphereLineProductData.product_scalarCurvature t ht _)

theorem QuotientSphereLineCertificate.scalarCurvature
    (q : QuotientSphereLineCertificate G) (t : ℝ) (ht : t < 0) (p : M) :
    (G.flow.connection t).scalarCurvature p = -1 / t := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.product_charted
  let := q.product.product_manifold
  let := q.quotient_topology
  let := q.quotient_charted
  let := q.quotient_manifold
  obtain ⟨e, he⟩ := q.flow_isometric_to_quotient
  have hflow := (G.flow.connection t).scalarCurvature_eq_of_local_isometry
    (q.quotient_connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun x _ => he t ht x) (mem_univ p)
  obtain ⟨z, hz⟩ := q.quotient_map_surjective (e p)
  have hprod := (q.product.product_connection t).scalarCurvature_eq_of_local_isometry
    (q.quotient_connection t) isOpen_univ q.quotient_map_smooth.contMDiffOn
    (fun x _ => q.quotient_metric_pullback t ht x) (mem_univ z)
  rw [hz] at hprod
  exact hflow.trans (hprod.symm.trans (q.product.product_scalarCurvature t ht z))

theorem ThreeDimensionalSolitonModel.scalarCurvature_of_noncompact [NoncompactSpace M]
    (C : ThreeDimensionalSolitonModel S G) (t : ℝ) (ht : t < 0) (p : M) :
    (G.flow.connection t).scalarCurvature p = -1 / t := by
  cases C with
  | compactRound c =>
    exact ((not_compactSpace_iff.mpr (inferInstance : NoncompactSpace M)) c.compact).elim
  | sphereLine c => exact c.scalarCurvature t ht p
  | quotientSphereLine q => exact q.scalarCurvature t ht p

theorem ThreeDimensionalSolitonModel.scalarCurvature_le_one_of_noncompact
    [NoncompactSpace M] (C : ThreeDimensionalSolitonModel S G)
    (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) (-1)) (p : M) :
    (G.flow.connection t).scalarCurvature p ≤ 1 := by
  rw [C.scalarCurvature_of_noncompact t (by linarith [ht.2]) p]
  rw [div_le_iff_of_neg (by linarith [ht.2] : t < 0)]
  linarith [ht.2]

end PoincareConjecture
