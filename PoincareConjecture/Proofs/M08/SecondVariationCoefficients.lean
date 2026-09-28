import PoincareConjecture.Proofs.M08.WeightedJacobiIdentities
import PoincareConjecture.Proofs.M08.SecondVariationSurface
import PoincareConjecture.Proofs.M08.SecondVariationGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance secondVariationCoefficientsDualGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCoefficientsDualSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationCoefficientsBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCoefficientsBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationCoefficientsEndGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCoefficientsEndSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationCoefficientsConnectionGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCoefficientsConnectionSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedSpace

theorem closedChartConnection_spatial_compatibility {J C : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w z : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q ↦ chartActionMetric F T x (s, q)) (extChartAt (𝓡 n) x y) v w z =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (closedChartConnection F T x C (s, extChartAt (𝓡 n) x y) v w) z +
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y) w
        (closedChartConnection F T x C (s, extChartAt (𝓡 n) x y) v z) := by
  have hq := (extChartAt (𝓡 n) x).map_source
    (show y ∈ (extChartAt (𝓡 n) x).source by simpa only [extChartAt_source] using hy)
  rw [(hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x) _
    (chartActionMetric_closed_contDiffOn F T x htime) hs hq).fderiv]
  exact chartActionMetric_spatial_compatibility F T htime hy hs v w z

theorem coordinateCurvature_pair {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (hsN : C ∈ 𝓝 s) (v a w z : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (coordinateCurvature (closedChartConnection F T x C)
          (s, extChartAt (𝓡 n) x y) v a w) z =
      (F.connection (T - s ^ 2)).curvatureTensor y
        (chartFrame x v y) (chartFrame x a y) (chartFrame x z y) (chartFrame x w y) := by
  let U := (extChartAt (𝓡 n) x).target
  have hq : extChartAt (𝓡 n) x y ∈ U := (extChartAt (𝓡 n) x).map_source
    (by simpa only [extChartAt_source] using hy)
  have hN : C ×ˢ U ∈ 𝓝 (s, extChartAt (𝓡 n) x y) :=
    prod_mem_nhds hsN ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq)
  unfold coordinateCurvature
  rw [curvatureTensor_chart F hM04 T hC htime hy hs,
    ← spatialWithinFDeriv_apply_of_mem_nhds _ hN v,
    ← spatialWithinFDeriv_apply_of_mem_nhds _ hN a,
    closedChartConnection_spatial_apply F T x hC htime hs hq,
    closedChartConnection_spatial_apply F T x hC htime hs hq]
  rfl

theorem chartActionPotential_hessian {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun q ↦ chartActionPotential F T x (s, q)))
        (extChartAt (𝓡 n) x y) v w -
      fderiv ℝ (fun q ↦ chartActionPotential F T x (s, q)) (extChartAt (𝓡 n) x y)
        (closedChartConnection F T x C (s, extChartAt (𝓡 n) x y) v w) =
      2 * s ^ 2 * (F.connection (T - s ^ 2)).hessian
        (F.connection (T - s ^ 2)).scalarCurvature y (chartFrame x v y) (chartFrame x w y) := by
  let U := (extChartAt (𝓡 n) x).target
  let P := chartActionPotential F T x
  let DP := spatialWithinFDeriv C U P
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) x
  have hq : extChartAt (𝓡 n) x y ∈ U := (extChartAt (𝓡 n) x).map_source
    (by simpa only [extChartAt_source] using hy)
  have hP : ContDiffOn ℝ ∞ P (C ×ˢ U) := chartActionPotential_closed_contDiffOn F hM04 T x htime
  have hfirst (q : EuclideanSpace ℝ (Fin n)) (hq : q ∈ U) :
      fderiv ℝ (fun r ↦ P (s, r)) q = DP (s, q) :=
    (hasFDerivAt_spatialWithin hU P hP hs hq).fderiv
  have hnear : fderiv ℝ (fun r ↦ P (s, r)) =ᶠ[𝓝 (extChartAt (𝓡 n) x y)]
      (fun r ↦ DP (s, r)) := by
    filter_upwards [hU.mem_nhds hq] with r hr
    exact hfirst r hr
  have hsecond := (hasFDerivAt_spatialWithin hU DP
    (spatialWithinFDeriv_contDiffOn hC hU P hP) hs hq).fderiv
  change fderiv ℝ (fderiv ℝ (fun q ↦ P (s, q))) (extChartAt (𝓡 n) x y) v w -
    fderiv ℝ (fun q ↦ P (s, q)) (extChartAt (𝓡 n) x y)
      (closedChartConnection F T x C (s, extChartAt (𝓡 n) x y) v w) = _
  rw [hnear.fderiv_eq, hsecond, hfirst _ hq]
  exact weighted_chart_hessian F hM04 T hC htime hy hs v w

theorem closedChartConnection_time_pair_interior {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (hsN : C ∈ 𝓝 s) (v w z : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (fderiv ℝ (closedChartConnection F T x C) (s, extChartAt (𝓡 n) x y) (1, 0) v w) z =
      2 * s * backwardConnectionVariationPairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x w y) (chartFrame x z y) := by
  have hq := (extChartAt (𝓡 n) x).map_source
    (show y ∈ (extChartAt (𝓡 n) x).source by simpa only [extChartAt_source] using hy)
  have hN := prod_mem_nhds hsN ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq)
  rw [← timeWithinFDeriv_of_mem_nhds _ hN,
    closedChartConnection_time_apply F T x hC htime hs hq]
  exact closedChartChristoffel_time_eq_connectionVariation F hM04 T hC htime hy hs
    (subset_closure (mem_interior_iff_mem_nhds.mpr hN)) v w z

theorem chartActionMetric_time_pair_interior {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (hsN : C ∈ 𝓝 s) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) (1, 0) v w =
      4 * s * (F.connection (T - s ^ 2)).ricci y (chartFrame x v y) (chartFrame x w y) := by
  have hq := (extChartAt (𝓡 n) x).map_source
    (show y ∈ (extChartAt (𝓡 n) x).source by simpa only [extChartAt_source] using hy)
  have hN := prod_mem_nhds hsN ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq)
  rw [← timeWithinFDeriv_of_mem_nhds _ hN, chartActionMetric_timeWithin F hM04 T x hC htime hs hq]
  simp only [smul_apply, smul_eq_mul, chartRicciForm_at hM04 _ hy]

end PoincareConjecture.M08
