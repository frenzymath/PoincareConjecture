import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryHorizontalExtension
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinarySquarePath
import PoincareConjecture.Proofs.M34.Standard.ModelCurveExtension
import PoincareConjecture.Proofs.M34.Standard.OrdinaryHorizontalConnection











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

noncomputable section

variable {n : ℕ} {I : SpacetimeInterval}
  {F : RicciFlow n (EuclideanSpace ℝ (Fin n)) I.domain}



def ordinarySquareVelocityExtension {T tau : ℝ}
    (q : BackwardTimePath F T 0 tau) (A : SqrtRegularPath q) :
    ParametricAlongCurveExtensionOn (n := n) (sqrtParameterInterval 0 tau) A.curve
      (curveVelocityWithin (n := n) A.curve (sqrtParameterInterval 0 tau)) :=
  modelCurveVelocityExtension A.curve (sqrtParameterInterval 0 tau) A.domain
    A.open_domain A.interval_subset
    (by simpa only [sqrtParameterInterval, Real.sqrt_zero] using
      (uniqueDiffOn_Icc (Real.sqrt_pos.mpr q.ordered))) A.smooth

set_option backward.isDefEq.respectTransparency false in


def ordinarySquareExtension
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T tau : ℝ} (q : BackwardTimePath F T 0 tau) (A : SqrtRegularPath q) :
    M14PullbackExtension (ordinaryProductLGeometry R hRicci)
      (compatibleSquareCurve R.product.productCylinder T A.curve)
      (sqrtParameterInterval 0 tau)
      (compatibleSquareHorizontal R.product.productCylinder R.product.productMetric T A.curve) := by
  let B := ordinaryModelHorizontalExtension R hRicci
    (compatibleSquareCurve R.product.productCylinder T A.curve)
    (curveVelocity (n := n) A.curve) (sqrtParameterInterval 0 tau) A.domain
    A.open_domain A.interval_subset (model_curveVelocity_contDiffOn A.open_domain A.smooth)
  refine { B with agrees := ?_ }
  intro s _
  exact ordinaryProductHorizontalLift_cylinder R.product _ _ _

set_option backward.isDefEq.respectTransparency false in



theorem ordinarySquareExtension_covariantDerivative
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T tau : ℝ} (q : BackwardTimePath F T 0 tau) (A : SqrtRegularPath q)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval 0 tau) :
    M14HorizontalCovariantDerivative (ordinaryProductLGeometry R hRicci)
      (compatibleSquareCurve R.product.productCylinder T A.curve)
      (sqrtParameterInterval 0 tau)
      (compatibleSquareHorizontal R.product.productCylinder R.product.productMetric T A.curve)
      (ordinarySquareExtension R hRicci q A) s =
      R.product.productMetric.spatialTangentEquiv
        ((R.product.timeIntervals.interval I).realParam (T - s ^ 2)) (A.curve s)
        (pullbackCovariantDerivative F (fun r => T - r ^ 2) A.curve
          (curveVelocityWithin A.curve (sqrtParameterInterval 0 tau))
          (sqrtParameterInterval 0 tau) (ordinarySquareVelocityExtension q A) s) := by
  let : NormedAddCommGroup (TangentSpace (spacetimeModel n)
      (compatibleSquareCurve R.product.productCylinder T A.curve s)) :=
    inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
  let : NormedSpace ℝ (TangentSpace (spacetimeModel n)
      (compatibleSquareCurve R.product.productCylinder T A.curve s)) :=
    inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
  have hK : UniqueDiffOn ℝ (sqrtParameterInterval 0 tau) := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using
      (uniqueDiffOn_Icc (Real.sqrt_pos.mpr q.ordered))
  have hvel := (ordinarySquareVelocityExtension q A).agrees s hs
  change curveVelocity (n := n) A.curve s =
    curveVelocityWithin (n := n) A.curve (sqrtParameterInterval 0 tau) s at hvel
  have ha := model_curveVelocity_contDiffOn A.open_domain A.smooth
  have hpar0 := ordinaryProductHorizontalLift_hasDerivAt R.product
    (compatibleSquareCurve R.product.productCylinder T A.curve s)
    ((ha.contDiffAt (A.open_domain.mem_nhds (A.interval_subset hs))).differentiableAt
      (by simp)).hasDerivAt
  have hpar := hpar0.deriv
  have hd := compatibleSquareCurve_derivative R.product.productCylinder R.product.productMetric T
    (fun _ hr => ordinarySquarePath_clockMem q hr) hs (hK s hs)
    ((A.smooth.contMDiffAt (A.open_domain.mem_nhds (A.interval_subset hs))).mdifferentiableAt
      (by simp))
  change deriv (fun r => ordinaryProductHorizontalLift R.product
      (compatibleSquareCurve R.product.productCylinder T A.curve s)
      (curveVelocity (n := n) A.curve r)) s +
    rawHorizontalCovariantDerivative R.leafwiseConnection
      (fun z => ordinaryProductHorizontalLift R.product z (curveVelocity (n := n) A.curve s))
      (compatibleSquareCurve R.product.productCylinder T A.curve s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n)
        (compatibleSquareCurve R.product.productCylinder T A.curve)
        (sqrtParameterInterval 0 tau) s 1) = _
  rw [hpar, hd]
  dsimp only [compatibleSquareCurve, compatibleSquareHorizontal]
  rw [ordinaryProductHorizontalLift_rawDerivative R F.connection,
    ordinaryProductHorizontalLift_cylinder]
  dsimp only [pullbackCovariantDerivative, ordinarySquareVelocityExtension,
    modelCurveVelocityExtension]
  rw [(R.product.timeIntervals.interval I).realParam_val (ordinarySquarePath_clockMem q hs),
    ← hvel]
  exact (R.product.productMetric.spatialTangentEquiv _ _).map_add _ _ |>.symm

end

end PoincareConjecture.M34
