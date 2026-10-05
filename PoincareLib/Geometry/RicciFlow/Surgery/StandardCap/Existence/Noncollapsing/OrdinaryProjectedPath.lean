import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.OrdinaryProductCurvature

/-!
# Projection of actual generalized paths to the ordinary product

The actual projection differentiates the horizontal velocity and preserves
the scalar-plus-kinetic density on the open path interval. Endpoint-free
integral congruence retains the genuine finite action.
Source: Morgan-Tian Proposition 12.13, pp. 304-306, ordinary capture.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareMT.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)
  (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)

set_option backward.isDefEq.respectTransparency false in
/-- The projected curve's actual velocity is the spatial projection of
the given horizontal velocity (Proposition 12.13, pp. 304-306). -/
theorem ordinaryProjectedCurve_velocity {T a b : ℝ}
    {x y : (ordinaryProductLGeometry R hRicci).Point}
    (p : M14BackwardPath (ordinaryProductLGeometry R hRicci) T a b x y)
    {s : ℝ} (hs : s ∈ Ioo a b) :
    curveVelocity (ordinaryProductProjection R.product ∘ p.curve) s =
      mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R.product)
        (p.curve s) (p.horizontal_velocity s).val := by
  have hreg := (p.curve_regular.contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt
    (by norm_num)
  have hd := mfderiv_comp s
    (ordinaryProductProjection_contMDiff R.product |>.mdifferentiableAt (by simp)) hreg
  have hv := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hd
  change curveVelocity (ordinaryProductProjection R.product ∘ p.curve) s =
    mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R.product) (p.curve s)
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve s 1) at hv
  rw [p.derivative_eq s hs, map_add, map_neg] at hv
  have hzero : mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R.product)
      (p.curve s) ((ordinaryProductLGeometry R hRicci).spacetime.timeVector (p.curve s)) = 0 :=
    ordinaryProductProjection_timeVector_at R.product (p.curve s)
  rw [hzero, neg_zero, zero_add] at hv
  exact hv

/-- Projection preserves the actual L-density at every interior parameter,
with no endpoint derivative assertion (Proposition 12.13, pp. 304-306). -/
theorem ordinaryProjectedCurve_integrand {T a b : ℝ}
    {x y : (ordinaryProductLGeometry R hRicci).Point}
    (p : M14BackwardPath (ordinaryProductLGeometry R hRicci) T a b x y)
    {s : ℝ} (hs : s ∈ Ioo a b) :
    backwardLIntegrand F T (ordinaryProductProjection R.product ∘ p.curve) s =
      M14BackwardLIntegrand (ordinaryProductLGeometry R hRicci) p s := by
  have htime : (p.curve s).1.val = T - s := p.curve_time s (Ioo_subset_Icc_self hs)
  have hscalar := ordinaryProduct_scalar_eq R F.connection (p.curve s).1 (p.curve s).2
  rw [R.product.productCylinder_eq, htime] at hscalar
  have hmetric := ordinaryProductProjection_inner R.product (p.curve s)
    (p.horizontal_velocity s) (p.horizontal_velocity s)
  rw [htime] at hmetric
  change Real.sqrt s * ((F.connection (T - s)).scalarCurvature
    (ordinaryProductProjection R.product (p.curve s)) +
      (F.metric (T - s)).inner (ordinaryProductProjection R.product (p.curve s))
        (curveVelocity (ordinaryProductProjection R.product ∘ p.curve) s)
        (curveVelocity (ordinaryProductProjection R.product ∘ p.curve) s)) = _
  rw [ordinaryProjectedCurve_velocity R hRicci p hs, hmetric,
    ordinaryProductProjection_eq, hscalar]
  rfl

/-- An actual generalized path projects to an admissible ordinary path,
including its genuine action integrability (Proposition 12.13). -/
noncomputable def ordinaryProjectedPath {T a b : ℝ} (hT : T ∈ I.domain)
    {x y : (ordinaryProductLGeometry R hRicci).Point}
    (p : M14BackwardPath (ordinaryProductLGeometry R hRicci) T a b x y) :
    BackwardTimePath F T a b where
  curve := ordinaryProductProjection R.product ∘ p.curve
  nonnegative := p.tau_nonneg
  ordered := p.tau_lt
  terminal_mem := hT
  time_mem := by
    intro s hs
    exact (p.curve_time s hs) ▸ (p.curve s).1.property
  continuous := (ordinaryProductProjection_contMDiff R.product).continuous.comp_continuousOn
    p.curve_continuous
  regular := ((ordinaryProductProjection_contMDiff R.product).of_le (by simp)).comp_contMDiffOn
    p.curve_regular
  l_integrable := p.action_integrable.congr_uIoo (by
    rw [uIoo_of_le p.tau_lt.le]
    intro s hs
    exact (ordinaryProjectedCurve_integrand R hRicci p hs).symm)

/-- Projecting a path preserves its actual action integral
(Proposition 12.13, pp. 304-306). -/
theorem ordinaryProjectedPath_action {T a b : ℝ} (hT : T ∈ I.domain)
    {x y : (ordinaryProductLGeometry R hRicci).Point}
    (p : M14BackwardPath (ordinaryProductLGeometry R hRicci) T a b x y) :
    backwardLLength F T a b (ordinaryProjectedPath R hRicci hT p).curve =
      M14BackwardLAction (ordinaryProductLGeometry R hRicci) p := by
  apply intervalIntegral.integral_congr_Ioo_of_le p.tau_lt.le
  intro s hs
  exact ordinaryProjectedCurve_integrand R hRicci p hs

end PoincareMT.M34
