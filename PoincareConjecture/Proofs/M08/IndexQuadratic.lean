import PoincareConjecture.Proofs.M08.IndexPairAlgebra
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

set_option maxHeartbeats 1600000 in
theorem regularizedIndexPairDensity_self {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J) (α : ℝ → M)
    {s : ℝ} (hs : s ∈ Icc a b)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (Y DY : TangentSpace (𝓡 n) (α s)) :
    regularizedIndexPairDensity F T α (Icc a b) s Y Y DY DY =
      let A := curveVelocityWithin (n := n) α (Icc a b) s
      let connection := F.connection (T - s ^ 2)
      (F.metric (T - s ^ 2)).inner (α s) DY DY +
        connection.curvatureTensor (α s) Y A A Y +
        2 * s ^ 2 * connection.hessian connection.scalarCurvature (α s) Y Y -
        4 * s * ricciDerivativePairing connection (α s) Y A Y +
        2 * s * ricciDerivativePairing connection (α s) A Y Y := by
  let x := α s
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let coord := e.continuousLinearMapAt ℝ (α s)
  have hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ _
  have hframe (v : TangentSpace (𝓡 n) (α s)) : chartFrame x (coord v) (α s) = v :=
    e.symmL_continuousLinearMapAt hx v
  have hpair := regularizedIndexPairDensity_chart F hM04 T hab htime x α hs hx hα
    (coord Y) (coord Y) (coord DY) (coord DY)
  simp only [hframe] at hpair
  rw [hpair, chartActionMetric_apply F T hx, hframe]
  change _ + closedChartJacobiPotential F T x (Icc a b)
    (s, extChartAt (𝓡 n) x (α s)) (deriv ((extChartAt (𝓡 n) x) ∘ α) s)
      (coord Y) (coord Y) = _
  rw [closedChartJacobiPotential_identification F hM04 T (uniqueDiffOn_Icc hab) htime hx hs
    (mem_closure_interior_Icc_prod hab (isOpen_extChartAt_target (I := 𝓡 n) x) hs
      ((extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hx))),
    hframe, chartFrame_curveVelocityWithin hx (uniqueDiffOn_Icc hab s hs) hα]
  have hR := ((hM04.tensor_calculus n M (F.metric (T - s ^ 2))
    (F.connection (T - s ^ 2))).2.2.2.1 (α s) Y
      (curveVelocityWithin (n := n) α (Icc a b) s) Y
      (curveVelocityWithin (n := n) α (Icc a b) s)).1
  dsimp only
  rw [hR]
  unfold backwardConnectionVariationPairing
  ring

theorem secondVariationIndexDensity_eq_pair {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (hM04 : RicciFlowCurvatureTheory.{u}) (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V) {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    secondVariationIndexDensity V D s =
      regularizedIndexPairDensity F T V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂) s
        (squareVariationField V s) (squareVariationField V s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
          (squareVariationField V) (sqrtParameterInterval τ₁ τ₂) D.variation_extension s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
          (squareVariationField V) (sqrtParameterInterval τ₁ τ₂) D.variation_extension s) := by
  exact (regularizedIndexPairDensity_self F hM04 T
    (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
    (fun r hr ↦ p.time_mem _ (square_mem_backward_interval p hr)) V.baseSquareCurve hs
    (variationBaseSquare_mdifferentiableAt V hs) _ _).symm

set_option maxHeartbeats 1600000 in
theorem regularizedIndexPairDensity_quadratic {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J) (α : ℝ → M)
    {s : ℝ} (hs : s ∈ Icc a b)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (Y W DY DW : TangentSpace (𝓡 n) (α s)) (c : ℝ) :
    regularizedIndexPairDensity F T α (Icc a b) s (Y + c • W) (Y + c • W)
        (DY + c • DW) (DY + c • DW) =
      regularizedIndexPairDensity F T α (Icc a b) s Y Y DY DY +
        2 * c * regularizedIndexPairDensity F T α (Icc a b) s Y W DY DW +
        c ^ 2 * regularizedIndexPairDensity F T α (Icc a b) s W W DW DW := by
  let x := α s
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let coord := e.continuousLinearMapAt ℝ (α s)
  have hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ _
  have hframe (v : TangentSpace (𝓡 n) (α s)) : chartFrame x (coord v) (α s) = v :=
    e.symmL_continuousLinearMapAt hx v
  have hchart (U V DU DV : TangentSpace (𝓡 n) (α s)) :
      regularizedIndexPairDensity F T α (Icc a b) s U V DU DV =
        chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s)) (coord DU) (coord DV) +
          jacobiAlongPotential F T x (Icc a b) α s (coord U) (coord V) := by
    have h := regularizedIndexPairDensity_chart F hM04 T hab htime x α hs hx hα
      (coord U) (coord V) (coord DU) (coord DV)
    simpa only [hframe] using h
  have hsym := regularizedIndexPairDensity_symm F hM04 T hab htime α hs hα Y W DY DW
  simp only [hchart] at hsym ⊢
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  linear_combination -c * hsym

theorem regularizedIndexPairDensity_green_value {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (α : ℝ → M) (s : ℝ)
    (Y W DY DW DDY : TangentSpace (𝓡 n) (α s)) :
    regularizedIndexPairDensity F T α C s Y W DY DW +
        jacobiPairResidual F T α C s Y DY DDY W =
      (F.metric (T - s ^ 2)).inner (α s) DDY W +
        (F.metric (T - s ^ 2)).inner (α s) DY DW +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s) DY W := by
  have hzero : (F.connection (T - s ^ 2)).ricci (α s) 0 W = 0 := by
    have h := ricci_smul_left_of_curvatureTheory hM04 (F.connection (T - s ^ 2))
      (α s) (0 : ℝ) (0 : TangentSpace (𝓡 n) (α s)) W
    simpa only [zero_smul, zero_mul] using h
  unfold regularizedIndexPairDensity jacobiPairResidual
  simp only [map_zero, zero_apply, hzero, mul_zero, add_zero]
  ring

end PoincareConjecture.M08
