import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.AccelerationPair
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Potential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ConnectionTimeSurface
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.FirstVariationIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {J : Set ℝ} {F : RicciFlow 2 M J} {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}

theorem surfaceActionDensity_variationChart (V : LVariation F T τ₁ τ₂ p)
    {x : M} {z : ℝ × ℝ} (hz : z ∈ variationChartDomain V x) :
    surfaceActionDensity (chartActionMetric F T x) (chartActionPotential F T x)
      (variationChart V x) z = variationActionDensity V z := by
  unfold surfaceActionDensity
  change chartActionMetric F T x (z.1, extChartAt (𝓡 2) x (V.squareFamily z.1 z.2))
      (coordinatePartialS (variationChart V x) z) (coordinatePartialS (variationChart V x) z) / 2 +
    chartActionPotential F T x (z.1, extChartAt (𝓡 2) x (V.squareFamily z.1 z.2)) = _
  rw [chartActionMetric_apply F T hz.2, chartActionPotential_apply F T hz.2,
    variationChart_partialS_frame V hz]
  unfold variationActionDensity regularizedLIntegrand
  ring

theorem surfaceAccelerationBoundaryPair_variationChart (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V) {x : M} {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
    (ht : T - s ^ 2 ∈ interior J) :
    surfaceAccelerationBoundaryPair (chartActionMetric F T x)
        (Frame.chartConnectionBilinear (chartActionMetric F T x))
        (variationChart V x) (s, 0) = variationAccelerationBoundaryPair V D s := by
  unfold surfaceAccelerationBoundaryPair coordinateCovariantU
  change chartActionMetric F T x (s, extChartAt (𝓡 2) x (V.baseSquareCurve s))
    (coordinatePartialS (variationChart V x) (s, 0))
    (coordinatePartialU (coordinatePartialU (variationChart V x)) (s, 0) +
      Frame.chartConnection (chartActionMetric F T x)
        (s, variationChart V x (s, 0))
        (coordinatePartialU (variationChart V x) (s, 0))
        (coordinatePartialU (variationChart V x) (s, 0))) = _
  rw [chartActionMetric_apply F T hx, variationChart_baseVelocity V hs hx,
    ← variationEndpointAcceleration_chart V D hs hx (squareTime_mem_interior_preimage ht)]
  unfold variationAccelerationBoundaryPair
  rw [variationAccelerationField_eq V D hs]

set_option maxHeartbeats 1800000 in
theorem surfaceIndex_variationChart
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    {x : M} {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
    (ht : T - s ^ 2 ∈ interior J) :
    let C := sqrtParameterInterval τ₁ τ₂
    let G := chartActionMetric F T x
    let Γ := Frame.chartConnectionBilinear (chartActionMetric F T x)
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
  have hDY := variationCovariantField_chart V D hsC hx (squareTime_mem_interior_preimage ht)
  have hY := variationChart_squareVariationField V hsC hx
  have hA := variationChart_baseVelocity V hsC hx
  dsimp only
  change chartActionMetric F T x (s, extChartAt (𝓡 2) x (V.baseSquareCurve s))
      (coordinateCovariantS (Frame.chartConnectionBilinear (chartActionMetric F T x)) q (coordinatePartialU q) (s, 0))
      (coordinateCovariantS (Frame.chartConnectionBilinear (chartActionMetric F T x)) q (coordinatePartialU q) (s, 0)) +
    chartActionMetric F T x (s, extChartAt (𝓡 2) x (V.baseSquareCurve s))
      (coordinateCurvature (Frame.chartConnectionBilinear (chartActionMetric F T x))
        (s, extChartAt (𝓡 2) x (V.baseSquareCurve s)) Y A Y) A -
    chartActionMetric F T x (s, extChartAt (𝓡 2) x (V.baseSquareCurve s))
      (fderiv ℝ (Frame.chartConnectionBilinear (chartActionMetric F T x))
        (s, extChartAt (𝓡 2) x (V.baseSquareCurve s)) (1, 0) Y Y) A +
    (fderiv ℝ (fderiv ℝ (fun r ↦ chartActionPotential F T x (s, r)))
        (extChartAt (𝓡 2) x (V.baseSquareCurve s)) Y Y -
      fderiv ℝ (fun r ↦ chartActionPotential F T x (s, r))
        (extChartAt (𝓡 2) x (V.baseSquareCurve s))
        (Frame.chartConnectionBilinear (chartActionMetric F T x) (s, extChartAt (𝓡 2) x (V.baseSquareCurve s)) Y Y)) = _
  rw [coordinateCurvature_pair F T s x _ hx ht,
    chartConnectionBilinear_time_pairing F T s x _ hx ht]
  simp only [Frame.chartConnectionBilinear_apply]
  rw [chartActionPotential_hessian F T s hx ht, chartActionMetric_apply F T hx]
  unfold backwardConnectionVariationPairing
  have hRicSymm (u v w : TangentSpace (𝓡 2) (V.baseSquareCurve s)) :
      ricciDerivativePairing (F.connection (T - s ^ 2)) (V.baseSquareCurve s) u v w =
        ricciDerivativePairing (F.connection (T - s ^ 2)) (V.baseSquareCurve s) u w v := by
    rw [(F.connection (T - s ^ 2)).ricciDerivativePairing_surface,
      (F.connection (T - s ^ 2)).ricciDerivativePairing_surface,
      (F.metric (T - s ^ 2)).symm]
  rw [hRicSymm (chartFrame x Y (V.baseSquareCurve s))
    (chartFrame x Y (V.baseSquareCurve s)) (chartFrame x A (V.baseSquareCurve s))]
  change pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
      (squareVariationField V) C D.variation_extension s =
    chartFrame x (coordinateCovariantS (Frame.chartConnectionBilinear (chartActionMetric F T x)) q
      (coordinatePartialU q) (s, 0)) (V.baseSquareCurve s) at hDY
  rw [← hDY]
  dsimp only [A, Y, q]
  rw [hA, hY]
  unfold secondVariationIndexDensity
  ring

set_option maxHeartbeats 1800000 in
theorem surfaceEuler_variationChart
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2))
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    {x : M} {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
    (ht : T - s ^ 2 ∈ interior J) :
    let C := sqrtParameterInterval τ₁ τ₂
    let G := chartActionMetric F T x
    let Γ := Frame.chartConnectionBilinear (chartActionMetric F T x)
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
  let Γ := Frame.chartConnectionBilinear (chartActionMetric F T x)
  let Z := coordinateCovariantU Γ q (coordinatePartialU q) (s, 0)
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have hsN : C ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have hq := (extChartAt (𝓡 2) x).map_source
    (show V.baseSquareCurve s ∈ (extChartAt (𝓡 2) x).source by
      simpa only [extChartAt_source] using hx)
  have hpot := (hasFDerivAt_spatial (chartActionDomain_open F T x) _
    (chartActionPotential_contDiffOn F T hpotential x)
      ⟨squareTime_mem_interior_preimage ht, hq⟩).fderiv
  have hDA := variationCovariantVelocity_chart V D hsC hx (squareTime_mem_interior_preimage ht)
  have hZ : chartFrame x Z (V.baseSquareCurve s) = variationAccelerationField V D s := by
    rw [variationAccelerationField_eq V D hsC]
    exact (variationEndpointAcceleration_chart V D hsC hx (squareTime_mem_interior_preimage ht)).symm
  dsimp only
  change chartActionMetric F T x (s, extChartAt (𝓡 2) x (V.baseSquareCurve s))
      (coordinateCovariantS Γ q (coordinatePartialS q) (s, 0)) Z -
    fderiv ℝ (fun r ↦ chartActionPotential F T x (s, r))
      (extChartAt (𝓡 2) x (V.baseSquareCurve s)) Z +
    fderiv ℝ (chartActionMetric F T x) (s, extChartAt (𝓡 2) x (V.baseSquareCurve s))
      (1, 0) (coordinatePartialS q (s, 0)) Z = _
  rw [Frame.chartActionMetric_time_fderiv F T s x _ hx ht,
    hpot, chartActionPotential_spatial_apply F T hpotential hx ht,
    chartActionMetric_apply F T hx]
  change pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
      (curveVelocityWithin (n := 2) V.baseSquareCurve C) C D.velocity_extension s =
    chartFrame x (coordinateCovariantS Γ q (coordinatePartialS q) (s, 0))
      (V.baseSquareCurve s) at hDA
  rw [← hDA, hZ, variationChart_baseVelocity V hsC hx]
  rfl

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
