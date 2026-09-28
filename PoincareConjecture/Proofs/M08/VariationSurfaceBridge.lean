import PoincareConjecture.Proofs.M08.SecondVariationBoundary
import PoincareConjecture.Proofs.M08.SecondVariationCoefficients
import PoincareConjecture.Proofs.M08.VariationChartFields

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}

theorem surfaceActionDensity_variationChart (V : LVariation F T τ₁ τ₂ p)
    {x : M} {z : ℝ × ℝ} (hz : z ∈ variationChartDomain V x) :
    surfaceActionDensity (chartActionMetric F T x) (chartActionPotential F T x)
      (variationChart V x) z = variationActionDensity V z := by
  unfold surfaceActionDensity
  change chartActionMetric F T x (z.1, extChartAt (𝓡 n) x (V.squareFamily z.1 z.2))
      (coordinatePartialS (variationChart V x) z) (coordinatePartialS (variationChart V x) z) / 2 +
    chartActionPotential F T x (z.1, extChartAt (𝓡 n) x (V.squareFamily z.1 z.2)) = _
  rw [chartActionMetric_apply F T hz.2, chartActionPotential_apply F T hz.2,
    variationChart_partialS_frame V hz]
  unfold variationActionDensity regularizedLIntegrand
  ring

theorem surfaceAccelerationBoundaryPair_variationChart (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V) {x : M} {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    surfaceAccelerationBoundaryPair (chartActionMetric F T x)
        (closedChartConnection F T x (sqrtParameterInterval τ₁ τ₂))
        (variationChart V x) (s, 0) = variationAccelerationBoundaryPair V D s := by
  unfold surfaceAccelerationBoundaryPair coordinateCovariantU
  change chartActionMetric F T x (s, extChartAt (𝓡 n) x (V.baseSquareCurve s))
    (coordinatePartialS (variationChart V x) (s, 0))
    (coordinatePartialU (coordinatePartialU (variationChart V x)) (s, 0) +
      closedChartChristoffel F T x (sqrtParameterInterval τ₁ τ₂)
        (s, variationChart V x (s, 0))
        (coordinatePartialU (variationChart V x) (s, 0))
        (coordinatePartialU (variationChart V x) (s, 0))) = _
  rw [chartActionMetric_apply F T hx, variationChart_baseVelocity V hs hx,
    ← variationEndpointAcceleration_chart V D hs hx]
  unfold variationAccelerationBoundaryPair
  rw [variationAccelerationField_eq V D hs]

set_option maxHeartbeats 1800000 in
theorem surfaceIndex_variationChart (hM04 : RicciFlowCurvatureTheory.{u})
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    {x : M} {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    let C := sqrtParameterInterval τ₁ τ₂
    let G := chartActionMetric F T x
    let Γ := closedChartConnection F T x C
    let q := variationChart V x
    let z := (s, q (s, 0))
    let A := coordinatePartialS q (s, 0)
    let Y := coordinatePartialU q (s, 0)
    let DY := coordinateCovariantS Γ q (coordinatePartialU q) (s, 0)
    let P₀ := fun r ↦ chartActionPotential F T x (s, r)
    G z DY DY + G z (coordinateCurvature Γ z Y A Y) A -
        G z (fderiv ℝ Γ z (1, 0) Y Y) A +
        (fderiv ℝ (fderiv ℝ P₀) (q (s, 0)) Y Y -
          fderiv ℝ P₀ (q (s, 0)) (Γ z Y Y)) = secondVariationIndexDensity V D s := by
  let C := sqrtParameterInterval τ₁ τ₂
  let q := variationChart V x
  let A := coordinatePartialS q (s, 0)
  let Y := coordinatePartialU q (s, 0)
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have hsN : C ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have htime (r : ℝ) (hr : r ∈ C) : T - r ^ 2 ∈ J :=
    p.time_mem _ (square_mem_backward_interval p hr)
  have hDY := variationCovariantField_chart V D hsC hx
  have hY := variationChart_squareVariationField V hsC hx
  have hA := variationChart_baseVelocity V hsC hx
  dsimp only
  change chartActionMetric F T x (s, extChartAt (𝓡 n) x (V.baseSquareCurve s))
      (coordinateCovariantS (closedChartConnection F T x C) q (coordinatePartialU q) (s, 0))
      (coordinateCovariantS (closedChartConnection F T x C) q (coordinatePartialU q) (s, 0)) +
    chartActionMetric F T x (s, extChartAt (𝓡 n) x (V.baseSquareCurve s))
      (coordinateCurvature (closedChartConnection F T x C)
        (s, extChartAt (𝓡 n) x (V.baseSquareCurve s)) Y A Y) A -
    chartActionMetric F T x (s, extChartAt (𝓡 n) x (V.baseSquareCurve s))
      (fderiv ℝ (closedChartConnection F T x C)
        (s, extChartAt (𝓡 n) x (V.baseSquareCurve s)) (1, 0) Y Y) A +
    (fderiv ℝ (fderiv ℝ (fun r ↦ chartActionPotential F T x (s, r)))
        (extChartAt (𝓡 n) x (V.baseSquareCurve s)) Y Y -
      fderiv ℝ (fun r ↦ chartActionPotential F T x (s, r))
        (extChartAt (𝓡 n) x (V.baseSquareCurve s))
        (closedChartConnection F T x C (s, extChartAt (𝓡 n) x (V.baseSquareCurve s)) Y Y)) = _
  rw [coordinateCurvature_pair F hM04 T hC htime hx hsC hsN,
    closedChartConnection_time_pair_interior F hM04 T hC htime hx hsC hsN,
    chartActionPotential_hessian F hM04 T hC htime hx hsC,
    chartActionMetric_apply F T hx]
  unfold backwardConnectionVariationPairing
  rw [ricciDerivativePairing_chart_symm F hM04 T htime hx hsC Y Y A]
  change pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
      (squareVariationField V) C D.variation_extension s =
    chartFrame x (coordinateCovariantS (closedChartConnection F T x C) q
      (coordinatePartialU q) (s, 0)) (V.baseSquareCurve s) at hDY
  rw [← hDY]
  dsimp only [A, Y, q]
  rw [hA, hY]
  unfold secondVariationIndexDensity
  ring

set_option maxHeartbeats 1800000 in
theorem surfaceEuler_variationChart (hM04 : RicciFlowCurvatureTheory.{u})
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    {x : M} {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    let C := sqrtParameterInterval τ₁ τ₂
    let G := chartActionMetric F T x
    let Γ := closedChartConnection F T x C
    let q := variationChart V x
    let z := (s, q (s, 0))
    let A := coordinatePartialS q (s, 0)
    let Z := coordinateCovariantU Γ q (coordinatePartialU q) (s, 0)
    let DA := coordinateCovariantS Γ q (coordinatePartialS q) (s, 0)
    let P₀ := fun r ↦ chartActionPotential F T x (s, r)
    G z DA Z - fderiv ℝ P₀ (q (s, 0)) Z + fderiv ℝ G z (1, 0) A Z =
      regularizedEulerResidual F T V.baseSquareCurve C D.velocity_extension s
        (variationAccelerationField V D s) := by
  let C := sqrtParameterInterval τ₁ τ₂
  let q := variationChart V x
  let Γ := closedChartConnection F T x C
  let Z := coordinateCovariantU Γ q (coordinatePartialU q) (s, 0)
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have hsN : C ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have htime (r : ℝ) (hr : r ∈ C) : T - r ^ 2 ∈ J :=
    p.time_mem _ (square_mem_backward_interval p hr)
  have hq := (extChartAt (𝓡 n) x).map_source
    (show V.baseSquareCurve s ∈ (extChartAt (𝓡 n) x).source by
      simpa only [extChartAt_source] using hx)
  have hpot := (hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x) _
    (chartActionPotential_closed_contDiffOn F hM04 T x htime) hsC hq).fderiv
  have hDA := variationCovariantVelocity_chart V D hsC hx
  have hZ : chartFrame x Z (V.baseSquareCurve s) = variationAccelerationField V D s := by
    rw [variationAccelerationField_eq V D hsC]
    exact (variationEndpointAcceleration_chart V D hsC hx).symm
  dsimp only
  change chartActionMetric F T x (s, extChartAt (𝓡 n) x (V.baseSquareCurve s))
      (coordinateCovariantS Γ q (coordinatePartialS q) (s, 0)) Z -
    fderiv ℝ (fun r ↦ chartActionPotential F T x (s, r))
      (extChartAt (𝓡 n) x (V.baseSquareCurve s)) Z +
    fderiv ℝ (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (V.baseSquareCurve s))
      (1, 0) (coordinatePartialS q (s, 0)) Z = _
  rw [chartActionMetric_time_pair_interior F hM04 T hC htime hx hsC hsN,
    hpot, chartActionPotential_closed_spatial_apply F hM04 T htime hx hsC,
    chartActionMetric_apply F T hx]
  change pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
      (curveVelocityWithin (n := n) V.baseSquareCurve C) C D.velocity_extension s =
    chartFrame x (coordinateCovariantS Γ q (coordinatePartialS q) (s, 0))
      (V.baseSquareCurve s) at hDA
  rw [← hDA, hZ, variationChart_baseVelocity V hsC hx]
  rfl

end PoincareConjecture.M08
