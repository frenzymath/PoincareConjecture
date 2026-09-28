import PoincareConjecture.Proofs.M14.Sec6_2_EulerResidual










set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}



theorem firstVariation_euler_fixedInitial
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) R.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval a b, ∀ W,
      M14SquareRootEulerResidual G R E s W = 0)
    (V : M14LVariationData G p R) (hzero : M14VariationField V (Real.sqrt a) = 0) :
    HasDerivAt (M14VariationAction V)
      (G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
        (R.horizontal_velocity (Real.sqrt b)) (M14VariationField V (Real.sqrt b))) 0 := by
  obtain ⟨D⟩ := exists_variationDerivativeData V
  have hfirst := firstVariationIdentity hCoordinates hM12 V D
  have hres : M14FirstVariationResidualIntegral V D = 0 := by
    unfold M14FirstVariationResidualIntegral
    rw [← intervalIntegral.integral_zero (a := Real.sqrt a) (b := Real.sqrt b)]
    apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt p.tau_lt.le)
    intro s hs
    change -M14SquareRootEulerResidual G R D.base_extension s (M14VariationField V s) = 0
    rw [squareRootEulerResidual_extension_independent D.base_extension E
      (Ioo_subset_Icc_self hs), hEuler s (Ioo_subset_Icc_self hs), neg_zero]
  simpa only [M14FirstVariationIdentity, hres, add_zero, M14FirstVariationBoundaryTerm,
    M14SquareRootVelocity, hzero, map_zero, sub_zero] using hfirst

end PoincareConjecture.M14
