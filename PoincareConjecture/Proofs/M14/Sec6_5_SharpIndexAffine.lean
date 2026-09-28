import PoincareConjecture.Proofs.M14.Sec6_4_PullbackLinearity
import PoincareConjecture.Proofs.M14.Sec6_4_IndexAlgebra
import PoincareConjecture.Proofs.M14.Sec6_4_IndexJacobi

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  (R : M14SquareRootPath G p)

theorem pullbackIndexIntegral_affine
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {Y Z : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Z) (c : ℝ) :
    (∫ s in Real.sqrt a..Real.sqrt b,
      pullbackIndexPairDensity R (affinePullbackExtension EY EZ c)
        (affinePullbackExtension EY EZ c) s) =
      (∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EY EY s) +
        2 * c * (∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EY EZ s) +
        c ^ 2 * (∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EZ EZ s) := by
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hI {A B : ∀ s, G.Horizontal (R.curve s)}
      (EA : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) A)
      (EB : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) B) :
      IntervalIntegrable (pullbackIndexPairDensity R EA EB) volume
        (Real.sqrt a) (Real.sqrt b) :=
    (pullbackIndexPairDensity_contDiffOn R (jacobiFieldDataOfExtension hCoordinates EA)
      EB hM04 hM12).continuousOn.intervalIntegrable_of_Icc hab.le
  have hYY := hI EY EY
  have hYZ := hI EY EZ
  have hZZ := hI EZ EZ
  calc
    _ = ∫ s in Real.sqrt a..Real.sqrt b,
        pullbackIndexPairDensity R EY EY s +
          2 * c * pullbackIndexPairDensity R EY EZ s +
          c ^ 2 * pullbackIndexPairDensity R EZ EZ s := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab.le
      intro s hs
      simp only [pullbackIndexPairDensity,
        horizontalCovariantDerivative_affine EY EZ c (Ioo_subset_Icc_self hs)]
      exact horizontalIndexPairDensity_quadratic R hM04 hM12 (Ioo_subset_Icc_self hs)
        (Y s) (Z s) _ _ c
    _ = _ := by
      rw [intervalIntegral.integral_add (hYY.add (hYZ.const_mul _)) (hZZ.const_mul _),
        intervalIntegral.integral_add hYY (hYZ.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end PoincareConjecture.M14
