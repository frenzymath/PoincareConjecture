import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartDifferential
import PoincareConjecture.Proofs.M14.Sec6_5_HessianIndexComparison









set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}




theorem positiveStart_hessian_le_pullback_index
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hp : M14IsMinimizing p)
    (U : Set G.Point) (hU : IsOpen U) (hy : y ∈ U)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T a x) U)
    (hq : G.spacetime.timeFunction (R.curve (Real.sqrt b)) = T - b)
    {Y : ∀ r, G.Horizontal (R.curve r)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (hleft : Y (Real.sqrt a) = 0) :
    M14ReducedLengthHessianPairing G ⟨R.curve (Real.sqrt b), hq⟩
        (M14ReducedLengthAt G T a x) (Y (Real.sqrt b)) (Y (Real.sqrt b)) ≤
      (∫ r in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EY EY r) /
        (2 * Real.sqrt b) := by
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hpoint : R.curve (Real.sqrt b) = y := by
    rw [R.agrees _ hs, Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le), p.curve_end]
  have hRU : R.curve (Real.sqrt b) ∈ U := by rwa [hpoint]
  have hY := pullbackExtension_field_contMDiffOn EY (R.smooth.mono R.interval_subset)
  obtain ⟨V, hfix, hfield, _⟩ :=
    exists_initialFixed_variation_of_smooth_horizontalField R hM12 Y hY hleft
  obtain ⟨D⟩ := exists_variationDerivativeData V
  have hgap := isLocalMin_variationAction_gap_of_smooth_minimizing hM12 V hp hfix U hU hy hf
  have h := variation_hessian_le_index hCoordinates hM04 hM12 V D hp hfix
    (M14ReducedLengthAt G T a x) U hU hRU hf hgap
      (positiveStart_horizontal_differential hCoordinates hM12 hp U hU hy hf) hq
  rwa [secondVariationIndexForm_eq_of_field V D EY hfield, hfield _ hs] at h

end PoincareConjecture.M14
