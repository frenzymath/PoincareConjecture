import PoincareConjecture.Proofs.M08.WeightedJacobiCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance weightedJacobiIdentitiesDualGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiIdentitiesDualSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedJacobiIdentitiesBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiIdentitiesBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedJacobiIdentitiesEndGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiIdentitiesEndSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedJacobiIdentitiesConnectionGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiIdentitiesConnectionSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1600000 in
theorem weighted_chart_hessian {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w : EuclideanSpace ℝ (Fin n)) :
    chartHessianForm (closedChartConnection F T x C (s, extChartAt (𝓡 n) x y))
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
          (chartActionPotential F T x) (s, extChartAt (𝓡 n) x y))
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
          (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
            (chartActionPotential F T x)) (s, extChartAt (𝓡 n) x y)) v w =
      2 * s ^ 2 * (F.connection (T - s ^ 2)).hessian
        (F.connection (T - s ^ 2)).scalarCurvature y (chartFrame x v y) (chartFrame x w y) := by
  let e := extChartAt (𝓡 n) x
  let U := e.target
  let P := chartActionPotential F T x
  let f := (F.connection (T - s ^ 2)).scalarCurvature
  let f₀ := f ∘ e.symm
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) x
  have hq : e y ∈ U := e.map_source (by simpa only [e, extChartAt_source] using hy)
  have hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f :=
    fun p ↦ scalarCurvature_slice_contMDiffAt_of_mem F hM04 (htime s hs) p
  have hf₀ (q : EuclideanSpace ℝ (Fin n)) (hq : q ∈ U) : ContDiffAt ℝ ∞ f₀ q :=
    (hf.contMDiffAt.comp q
      (((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x) q hq).contMDiffAt
        (hU.mem_nhds hq))).contDiffAt
  have hP := chartActionPotential_closed_contDiffOn F hM04 T x htime
  have hD := spatialWithinFDeriv_contDiffOn hC hU P hP
  have hfirst (q : EuclideanSpace ℝ (Fin n)) (hq : q ∈ U) :
      spatialWithinFDeriv C U P (s, q) = (2 * s ^ 2) • fderiv ℝ f₀ q := by
    have hd := hasFDerivAt_spatialWithin hU P hP hs hq
    have hscaled : HasFDerivAt (fun r ↦ P (s, r))
        ((2 * s ^ 2) • fderiv ℝ f₀ q) q := by
      convert ((hf₀ q hq).differentiableAt (by simp)).hasFDerivAt.const_smul (2 * s ^ 2)
        using 1 <;> rfl
    exact hd.unique hscaled
  have hfd : DifferentiableAt ℝ (fderiv ℝ f₀) (e y) :=
    ((hf₀ (e y) hq).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hsecond : spatialWithinFDeriv C U (spatialWithinFDeriv C U P) (s, e y) =
      (2 * s ^ 2) • fderiv ℝ (fderiv ℝ f₀) (e y) := by
    have hd := hasFDerivAt_spatialWithin hU _ hD hs hq
    have hscaled : HasFDerivAt (fun r ↦ spatialWithinFDeriv C U P (s, r))
        ((2 * s ^ 2) • fderiv ℝ (fderiv ℝ f₀) (e y)) (e y) := by
      apply (hfd.hasFDerivAt.const_smul (2 * s ^ 2)).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hq] with r hr
      exact hfirst r hr
    exact hd.unique hscaled
  change chartHessianForm (closedChartConnection F T x C (s, e y))
      (spatialWithinFDeriv C U P (s, e y))
      (spatialWithinFDeriv C U (spatialWithinFDeriv C U P) (s, e y)) v w = _
  rw [chartHessianForm_apply, hfirst (e y) hq, hsecond,
    closedChartConnection_apply, hessian_chart F T htime hy hs f hf]
  simp only [smul_apply, smul_eq_mul]
  dsimp only [f₀, f, e]
  ring

theorem chartCurvatureAlong_pair {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (A v w : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (chartCurvatureAlong (closedChartConnection F T x C (s, extChartAt (𝓡 n) x y))
          (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
            (closedChartConnection F T x C) (s, extChartAt (𝓡 n) x y)) A v) w =
      (F.connection (T - s ^ 2)).curvatureTensor y
        (chartFrame x v y) (chartFrame x A y) (chartFrame x w y) (chartFrame x A y) := by
  have hq : extChartAt (𝓡 n) x y ∈ (extChartAt (𝓡 n) x).target :=
    (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hy)
  rw [curvatureTensor_chart F hM04 T hC htime hy hs,
    chartCurvatureAlong_apply,
    closedChartConnection_spatial_apply F T x hC htime hs hq,
    closedChartConnection_spatial_apply F T x hC htime hs hq]
  simp only [closedChartConnection_apply]

set_option maxHeartbeats 1200000 in
theorem closedChartJacobiPotential_identification {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C)
    (hcl : (s, extChartAt (𝓡 n) x y) ∈
      closure (interior (C ×ˢ (extChartAt (𝓡 n) x).target)))
    (A v w : EuclideanSpace ℝ (Fin n)) :
    closedChartJacobiPotential F T x C (s, extChartAt (𝓡 n) x y) A v w =
      -(F.connection (T - s ^ 2)).curvatureTensor y
        (chartFrame x v y) (chartFrame x A y) (chartFrame x w y) (chartFrame x A y) +
      2 * s * backwardConnectionVariationPairing (F.connection (T - s ^ 2)) y
        (chartFrame x A y) (chartFrame x v y) (chartFrame x w y) +
      2 * s ^ 2 * (F.connection (T - s ^ 2)).hessian
        (F.connection (T - s ^ 2)).scalarCurvature y (chartFrame x v y) (chartFrame x w y) -
      4 * s * ricciDerivativePairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x A y) (chartFrame x w y) := by
  have hq : extChartAt (𝓡 n) x y ∈ (extChartAt (𝓡 n) x).target :=
    (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hy)
  unfold closedChartJacobiPotential
  rw [weightedChartPotential_apply,
    chartCurvatureAlong_pair F hM04 T hC htime hy hs,
    ← chartHessianForm_apply,
    weighted_chart_hessian F hM04 T hC htime hy hs,
    closedChartConnection_time_apply F T x hC htime hs hq,
    closedChartChristoffel_time_eq_connectionVariation F hM04 T hC htime hy hs hcl]
  unfold backwardConnectionVariationPairing
  rw [ricciDerivativePairing_chart_symm F hM04 T htime hy hs v w A,
    ricciDerivativePairing_chart_symm F hM04 T htime hy hs w v A]
  ring

end PoincareConjecture.M08
