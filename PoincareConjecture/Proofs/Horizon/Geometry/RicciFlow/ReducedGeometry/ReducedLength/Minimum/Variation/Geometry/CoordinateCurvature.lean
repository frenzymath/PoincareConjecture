import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Variation.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.AdaptedCoefficient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.CoefficientRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Surface












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local instance coordinateCurvatureDualGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance coordinateCurvatureDualSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance coordinateCurvatureBilinearGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance coordinateCurvatureBilinearSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance coordinateCurvatureEndGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance coordinateCurvatureEndSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedSpace
local instance coordinateCurvatureConnectionGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedAddCommGroup
local instance coordinateCurvatureConnectionSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedSpace

theorem chartActionMetric_eq_pullbackCoefficients
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x : M)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target) :
    chartActionMetric F T x (s, q) =
      (F.metric (T - s ^ 2)).pullbackCoefficients (extChartAt (𝓡 n) x).symm q := by
  let e := extChartAt (𝓡 n) x
  have hy : e.symm q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    simpa only [e, extChartAt_source] using e.map_target hq
  ext v w
  have h := chartActionMetric_apply F T hy s v w
  rw [e.right_inv hq, chartFrame_inverse_derivative hy v,
    chartFrame_inverse_derivative hy w, e.right_inv hq] at h
  exact h



theorem chartConnection_eq_coordinateChristoffel
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x : M)
    (ht : T - s ^ 2 ∈ interior J)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target)
    (v w : EuclideanSpace ℝ (Fin n)) :
    chartConnection (chartActionMetric F T x) (s, q) v w =
      coordinateChristoffel
        ((F.metric (T - s ^ 2)).pullbackCoefficients (extChartAt (𝓡 n) x).symm)
        q v w := by
  let G := chartActionMetric F T x
  let B := (F.metric (T - s ^ 2)).pullbackCoefficients (extChartAt (𝓡 n) x).symm
  have hz : (s, q) ∈ chartActionDomain F T x :=
    ⟨squareTime_mem_interior_preimage ht, hq⟩
  have hG : DifferentiableAt ℝ G (s, q) :=
    (((chartActionMetric_contDiffOn F T x) _ hz).contDiffAt
      ((chartActionDomain_open F T x).mem_nhds hz)).differentiableAt (by simp)
  have hmetric : G (s, q) = B q := chartActionMetric_eq_pullbackCoefficients F T s x hq
  have heq : (fun r => G (s, r)) =ᶠ[𝓝 q] B := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq] with r hr
    exact chartActionMetric_eq_pullbackCoefficients F T s x hr
  have hslice := hG.hasFDerivAt.comp q
    ((hasFDerivAt_const s q).prodMk (hasFDerivAt_id q))
  have hD (a b c : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ B q a b c = fderiv ℝ G (s, q) (0, a) b c := by
    rw [← heq.fderiv_eq]
    simpa [Function.comp_def] using congrArg (fun L => L a b c) hslice.fderiv
  have hsym : ∀ᶠ r in 𝓝 (s, q), ∀ a b, G r a b = G r b a := by
    filter_upwards [(chartActionDomain_open F T x).mem_nhds hz] with r hr
    exact chartActionMetric_symm F T x hr
  have hswap := fderiv_bilinear_symm G (s, q) hG hsym (0, w) v
  have hInv : (B q).IsInvertible := (F.metric (T - s ^ 2)).isInvertible_chartCoefficients x hq
  apply hInv.injective
  ext z
  have hpair : B q (coordinateChristoffel B q v w) z =
      (2⁻¹ : ℝ) * (fderiv ℝ B q v w z + fderiv ℝ B q w z v -
        fderiv ℝ B q z v w) := by
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L z)
      (hInv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B q) v w))
    simpa [coordinateChristoffel, metricKoszulCovector] using h
  calc
    B q (chartConnection G (s, q) v w) z =
        (1 / 2 : ℝ) * (fderiv ℝ G (s, q) (0, v) w z +
          fderiv ℝ G (s, q) (0, w) v z - fderiv ℝ G (s, q) (0, z) v w) := by
      rw [← hmetric]
      exact chartConnection_pairing G (s, q) (chartActionMetric_pos F T x hz) v w z
    _ = B q (coordinateChristoffel B q v w) z := by
      rw [hpair, hD, hD, hD, hswap z]
      ring

private theorem coordinateCurvature_eq_pullbackCurvature
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x : M)
    (ht : T - s ^ 2 ∈ interior J)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target)
    (v a w : EuclideanSpace ℝ (Fin n)) :
    coordinateCurvature (chartConnectionBilinear (chartActionMetric F T x)) (s, q) v a w =
      CoordinateExponential.coordinateCurvature
        ((F.metric (T - s ^ 2)).pullbackCoefficients (extChartAt (𝓡 n) x).symm)
        q v a w := by
  let G := chartActionMetric F T x
  let Γ := chartConnectionBilinear G
  let B := (F.metric (T - s ^ 2)).pullbackCoefficients (extChartAt (𝓡 n) x).symm
  have hz : (s, q) ∈ chartActionDomain F T x :=
    ⟨squareTime_mem_interior_preimage ht, hq⟩
  have hΓ : DifferentiableAt ℝ Γ (s, q) :=
    (((chartConnectionBilinear_contDiffOn G (chartActionDomain F T x)
      (chartActionDomain_open F T x) (chartActionMetric_contDiffOn F T x)
      (fun z hz => chartActionMetric_pos F T x hz)) _ hz).contDiffAt
        ((chartActionDomain_open F T x).mem_nhds hz)).differentiableAt (by simp)
  have heq (b c : EuclideanSpace ℝ (Fin n)) :
      (fun r => Γ (s, r) b c) =ᶠ[𝓝 q] fun r => coordinateChristoffel B r b c := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq] with r hr
    exact chartConnection_eq_coordinateChristoffel F T s x ht hr b c
  have hvalue (b c : EuclideanSpace ℝ (Fin n)) :
      Γ (s, q) b c = coordinateChristoffel B q b c := (heq b c).eq_of_nhds
  have hD (d b c : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun r => coordinateChristoffel B r b c) q d =
        fderiv ℝ Γ (s, q) (0, d) b c := by
    rw [← (heq b c).fderiv_eq]
    have hs := hΓ.hasFDerivAt.comp q
      ((hasFDerivAt_const s q).prodMk (hasFDerivAt_id q))
    have hv := (hs.clm_apply (hasFDerivAt_const b q)).clm_apply (hasFDerivAt_const c q)
    simpa using congrArg (fun L => L d) hv.fderiv
  change coordinateCurvature Γ (s, q) v a w =
    CoordinateExponential.coordinateCurvature B q v a w
  unfold coordinateCurvature CoordinateExponential.coordinateCurvature
  rw [hD, hD, hvalue, hvalue, hvalue, hvalue]
  abel



theorem coordinateCurvature_pair
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (v a w z : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (coordinateCurvature (chartConnectionBilinear (chartActionMetric F T x))
          (s, extChartAt (𝓡 n) x y) v a w) z =
      (F.connection (T - s ^ 2)).curvatureTensor y
        (chartFrame x v y) (chartFrame x a y) (chartFrame x z y) (chartFrame x w y) := by
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  let c := extChartAt (𝓡 n) x
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hy' : y ∈ c.source := by simpa only [c, extChartAt_source] using hy
  have hq : c y ∈ c.target := c.map_source hy'
  have hframe (b : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) c y (chartFrame x b y) = b := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy]
    exact e.continuousLinearMapAt_symmL hy b
  have hR := ConnectionVariation.coordinateCurvature_in_chart g D x hy'
    (chartFrame x v y) (chartFrame x a y) (chartFrame x w y)
  change CoordinateExponential.coordinateCurvature (g.pullbackCoefficients c.symm) (c y)
      (mfderiv (𝓡 n) (𝓡 n) c y (chartFrame x v y))
      (mfderiv (𝓡 n) (𝓡 n) c y (chartFrame x a y))
      (mfderiv (𝓡 n) (𝓡 n) c y (chartFrame x w y)) =
    mfderiv (𝓡 n) (𝓡 n) c y
      (D.curvature y (chartFrame x v y) (chartFrame x a y) (chartFrame x w y)) at hR
  rw [hframe, hframe, hframe] at hR
  have hvector : chartFrame x
      (coordinateCurvature (chartConnectionBilinear (chartActionMetric F T x))
        (s, c y) v a w) y =
      D.curvature y (chartFrame x v y) (chartFrame x a y) (chartFrame x w y) := by
    rw [coordinateCurvature_eq_pullbackCurvature F T s x ht hq, hR]
    unfold chartFrame
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy]
    exact e.symmL_continuousLinearMapAt hy _
  rw [chartActionMetric_apply F T hy, hvector]
  rfl

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
