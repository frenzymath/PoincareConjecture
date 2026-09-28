import PoincareConjecture.Proofs.M08.JacobiLocalUniqueness
import PoincareConjecture.Proofs.M08.SecondVariationCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem scalarHessian_chart_symm {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).hessian (F.connection (T - s ^ 2)).scalarCurvature y
        (chartFrame x v y) (chartFrame x w y) =
      (F.connection (T - s ^ 2)).hessian (F.connection (T - s ^ 2)).scalarCurvature y
        (chartFrame x w y) (chartFrame x v y) := by
  let f := (F.connection (T - s ^ 2)).scalarCurvature
  let e := extChartAt (𝓡 n) x
  have hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f :=
    fun p ↦ scalarCurvature_slice_contMDiffAt_of_mem F hM04 (htime s hs) p
  have hq : e y ∈ e.target := e.map_source
    (by simpa only [e, extChartAt_source] using hy)
  have hf₀ : ContDiffAt ℝ ∞ (f ∘ e.symm) (e y) :=
    (hf.contMDiffAt.comp (e y)
      (((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x) _ hq).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq))).contDiffAt
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  change (F.connection (T - s ^ 2)).hessian f y (chartFrame x v y) (chartFrame x w y) = _
  rw [hessian_chart F T htime hy hs f hf v w,
    hessian_chart F T htime hy hs f hf w v,
    closedChartChristoffel_symm F T htime hy hs v w]
  exact congrArg (fun q : ℝ ↦ q -
    fderiv ℝ (f ∘ e.symm) (e y) (closedChartChristoffel F T x C (s, e y) w v))
      ((hf₀.isSymmSndFDerivAt htwo) v w)

set_option maxHeartbeats 1200000 in
theorem closedChartJacobiPotential_symm {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C)
    (hcl : (s, extChartAt (𝓡 n) x y) ∈
      closure (interior (C ×ˢ (extChartAt (𝓡 n) x).target)))
    (A v w : EuclideanSpace ℝ (Fin n)) :
    closedChartJacobiPotential F T x C (s, extChartAt (𝓡 n) x y) A v w =
      closedChartJacobiPotential F T x C (s, extChartAt (𝓡 n) x y) A w v := by
  rw [closedChartJacobiPotential_identification F hM04 T hC htime hy hs hcl,
    closedChartJacobiPotential_identification F hM04 T hC htime hy hs hcl]
  have hR := ((hM04.tensor_calculus n M (F.metric (T - s ^ 2))
    (F.connection (T - s ^ 2))).2.2.2.1 y
      (chartFrame x v y) (chartFrame x A y) (chartFrame x w y) (chartFrame x A y)).2.1
  have hH := scalarHessian_chart_symm F hM04 T htime hy hs v w
  have hN₁ := ricciDerivativePairing_chart_symm F hM04 T htime hy hs A v w
  unfold backwardConnectionVariationPairing
  rw [hR, hH, hN₁]
  ring

def regularizedIndexPairDensity {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (C : Set ℝ) (s : ℝ)
    (Y W DY DW : TangentSpace (𝓡 n) (α s)) : ℝ :=
  (F.metric (T - s ^ 2)).inner (α s) DY DW -
    jacobiPairResidual F T α C s Y 0 0 W

theorem regularizedIndexPairDensity_chart {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J) (x : M) (α : ℝ → M)
    {s : ℝ} (hs : s ∈ Icc a b)
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (y w dy dw : EuclideanSpace ℝ (Fin n)) :
    regularizedIndexPairDensity F T α (Icc a b) s (chartFrame x y (α s))
        (chartFrame x w (α s)) (chartFrame x dy (α s)) (chartFrame x dw (α s)) =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s)) dy dw +
        jacobiAlongPotential F T x (Icc a b) α s y w := by
  have hres := jacobiPairResidual_chart F hM04 T hab htime x α hs hx hα y 0 0 w
  have hzero : chartFrame (n := n) x 0 (α s) = 0 := (by simp only [chartFrame, map_zero])
  rw [hzero] at hres
  unfold regularizedIndexPairDensity
  rw [hres, ← chartActionMetric_apply F T hx s dy dw]
  simp only [map_zero, zero_apply, zero_sub, zero_add, add_zero, sub_neg_eq_add]

theorem regularizedIndexPairDensity_symm {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J) (α : ℝ → M)
    {s : ℝ} (hs : s ∈ Icc a b)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (Y W DY DW : TangentSpace (𝓡 n) (α s)) :
    regularizedIndexPairDensity F T α (Icc a b) s Y W DY DW =
      regularizedIndexPairDensity F T α (Icc a b) s W Y DW DY := by
  let x := α s
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let coord := e.continuousLinearMapAt ℝ (α s)
  have hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ _
  have hframe (v : TangentSpace (𝓡 n) (α s)) : chartFrame x (coord v) (α s) = v :=
    e.symmL_continuousLinearMapAt hx v
  have h₁ := regularizedIndexPairDensity_chart F hM04 T hab htime x α hs hx hα
    (coord Y) (coord W) (coord DY) (coord DW)
  have h₂ := regularizedIndexPairDensity_chart F hM04 T hab htime x α hs hx hα
    (coord W) (coord Y) (coord DW) (coord DY)
  simp only [hframe] at h₁ h₂
  rw [h₁, h₂, chartActionMetric_symm_at F T hx s (coord DY) (coord DW)]
  congr 1
  exact closedChartJacobiPotential_symm F hM04 T (uniqueDiffOn_Icc hab) htime hx hs
    (mem_closure_interior_Icc_prod hab (isOpen_extChartAt_target (I := 𝓡 n) x) hs
      ((extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hx)))
    (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (coord Y) (coord W)

end PoincareConjecture.M08

