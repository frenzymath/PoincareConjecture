import PoincareConjecture.Proofs.M35.CapGeometry.RoundProductConnection









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)



theorem product_euclideanConnection_fderiv
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    (hmetric : ∀ x u v : V,
      g.inner x u v = h.inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    (x u v w : V) :
    fderiv ℝ (D.euclideanConnection u v) x w =
      cylinderCoordinateEquiv.symm
        (fderiv ℝ (Dh.euclideanConnection (cylinderCoordinateEquiv u).1
          (cylinderCoordinateEquiv v).1) (cylinderCoordinateEquiv x).1
            (cylinderCoordinateEquiv w).1, 0) := by
  let H := (ContinuousLinearMap.fst ℝ E2 ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  let J := cylinderCoordinateEquiv.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E2 ℝ)
  let gamma := Dh.euclideanConnection (H u) (H v)
  have he : D.euclideanConnection u v = fun y => J (gamma (H y)) := by
    funext y
    exact product_euclideanConnection D Dh (Eventually.of_forall hmetric) u v
  have hd := J.hasFDerivAt.comp x
    (((Dh.contDiffAt_euclideanConnection (H x) (H u) (H v)).differentiableAt
      (by simp)).hasFDerivAt.comp x H.hasFDerivAt)
  rw [he]
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using!
    congrArg (fun A : V →L[ℝ] V => A w) hd.fderiv



theorem product_curvature
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    (hmetric : ∀ x u v : V,
      g.inner x u v = h.inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    (x u v w : V) :
    D.curvature x u v w = cylinderCoordinateEquiv.symm
      (Dh.curvature (cylinderCoordinateEquiv x).1 (cylinderCoordinateEquiv u).1
        (cylinderCoordinateEquiv v).1 (cylinderCoordinateEquiv w).1, 0) := by
  rw [D.curvature_eq_euclideanConnection, Dh.curvature_eq_euclideanConnection,
    product_euclideanConnection_fderiv D Dh hmetric,
    product_euclideanConnection_fderiv D Dh hmetric]
  simp only [product_euclideanConnection D Dh (Eventually.of_forall hmetric),
    ContinuousLinearEquiv.apply_symm_apply]
  apply cylinderCoordinateEquiv.injective
  simp only [map_sub, map_add, ContinuousLinearEquiv.apply_symm_apply,
    Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_self]



theorem product_curvatureTensor
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    (hmetric : ∀ x u v : V,
      g.inner x u v = h.inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    (x u v w z : V) :
    D.curvatureTensor x u v w z =
      Dh.curvatureTensor (cylinderCoordinateEquiv x).1 (cylinderCoordinateEquiv u).1
        (cylinderCoordinateEquiv v).1 (cylinderCoordinateEquiv w).1
          (cylinderCoordinateEquiv z).1 := by
  rw [LeviCivitaData.curvatureTensor, product_curvature D Dh hmetric, hmetric]
  simp only [ContinuousLinearEquiv.apply_symm_apply, zero_mul, add_zero]
  rfl

end PoincareConjecture.M35
