import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinarySquareExtension
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryScalarDifferential












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

noncomputable section

variable {n : ℕ} {I : SpacetimeInterval}
  {F : RicciFlow n (EuclideanSpace ℝ (Fin n)) I.domain}

set_option backward.isDefEq.respectTransparency false in



theorem ordinarySquarePath_euler
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T tau : ℝ} (q : BackwardTimePath F T 0 tau) (A : RegularizedLGeodesicData q)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval 0 tau)
    (W : (ordinaryProductLGeometry R hRicci).Horizontal
      ((ordinarySquarePath R hRicci q A.path).curve s)) :
    M14SquareRootEulerResidual (ordinaryProductLGeometry R hRicci)
      (ordinarySquarePath R hRicci q A.path)
      (ordinarySquareExtension R hRicci q A.path) s W = 0 := by
  let t := (R.product.timeIntervals.interval I).realParam (T - s ^ 2)
  let x := A.path.curve s
  obtain ⟨w, rfl⟩ := (R.product.productMetric.spatialTangentEquiv t x).surjective W
  have htime : t.val = T - s ^ 2 :=
    (R.product.timeIntervals.interval I).realParam_val (ordinarySquarePath_clockMem q hs)
  have hK : UniqueDiffOn ℝ (sqrtParameterInterval 0 tau) := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using
      (uniqueDiffOn_Icc (Real.sqrt_pos.mpr q.ordered))
  have hind := PoincareConjecture.Proofs.M09.pullbackCovariantDerivative_extension_independent
    F (fun r => T - r ^ 2) A.path.curve _ (sqrtParameterInterval 0 tau)
    A.velocity_extension (ordinarySquareVelocityExtension q A.path) s hs (hK s hs)
    ((A.path.smooth.contMDiffAt
      (A.path.open_domain.mem_nhds (A.path.interval_subset hs))).mdifferentiableAt (by simp))
  have hvel := (ordinarySquareVelocityExtension q A.path).agrees s hs
  change curveVelocity (n := n) A.path.curve s =
    curveVelocityWithin (n := n) A.path.curve (sqrtParameterInterval 0 tau) s at hvel
  change R.product.spacetime.horizontalMetric.inner (R.product.productCylinder.toSpacetime (t, x))
      (M14HorizontalCovariantDerivative (ordinaryProductLGeometry R hRicci)
        (compatibleSquareCurve R.product.productCylinder T A.path.curve)
        (sqrtParameterInterval 0 tau)
        (compatibleSquareHorizontal R.product.productCylinder
          R.product.productMetric T A.path.curve)
        (ordinarySquareExtension R hRicci q A.path) s)
      (R.product.productMetric.spatialTangentEquiv t x w) -
    2 * s ^ 2 * mvfderiv (spacetimeModel n)
      (fun z : R.product.spacetime.Point => horizontalScalarCurvature R.leafwiseConnection z)
      (R.product.productCylinder.toSpacetime (t, x))
      (R.product.productMetric.spatialTangentEquiv t x w).val +
    4 * s * horizontalRicci R.leafwiseConnection (R.product.productCylinder.toSpacetime (t, x))
      (R.product.productMetric.spatialTangentEquiv t x (curveVelocity (n := n) A.path.curve s))
      (R.product.productMetric.spatialTangentEquiv t x w) = 0
  rw [ordinarySquareExtension_covariantDerivative R hRicci q A.path hs,
    ← ordinaryProduct_inner_eq R.product t x _ w,
    ordinaryProduct_scalarDifferential (F := F) R t x w,
    ← ordinaryProduct_ricci_eq R F.connection t x _ w, htime]
  have heq := A.equation s hs w
  unfold regularizedEulerResidual scalarCurvatureDifferential at heq
  rw [hind, ← hvel] at heq
  exact heq

end

end PoincareConjecture.M34
