import PoincareConjecture.Proofs.M08.ChartConnection
import PoincareConjecture.Proofs.M08.ChartConnectionVariation
import PoincareConjecture.Proofs.M08.FirstVariationIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

section Interior

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem spatialWithinFDeriv_apply_of_mem_nhds {C : Set ℝ} {U : Set E}
    (f : ℝ × E → H) {z : ℝ × E} (hz : C ×ˢ U ∈ 𝓝 z) (v : E) :
    spatialWithinFDeriv C U f z v = fderiv ℝ f z (0, v) := by
  unfold spatialWithinFDeriv
  rw [fderivWithin_of_mem_nhds hz]
  rfl

theorem timeWithinFDeriv_of_mem_nhds {C : Set ℝ} {U : Set E}
    (f : ℝ × E → H) {z : ℝ × E} (hz : C ×ˢ U ∈ 𝓝 z) :
    timeWithinFDeriv C U f z = fderiv ℝ f z (1, 0) := by
  unfold timeWithinFDeriv
  rw [fderivWithin_of_mem_nhds hz]

end Interior

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance secondVariationGeometryDualGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationGeometryDualSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationGeometryBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationGeometryBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1000000 in
theorem chartActionMetric_spatial_compatibility {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (u v w : EuclideanSpace ℝ (Fin n)) :
    spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x)
        (s, extChartAt (𝓡 n) x y) u v w =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) u v) w +
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        v (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) u w) := by
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hframe (z : EuclideanSpace ℝ (Fin n)) :=
    ((chartFrame_contMDiffOn x z y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt
        (by simp)
  have h := D.metricCompatible.mvfderiv_inner_eq (chartFrame x u) (hframe v) (hframe w)
  change mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x w p)) y
      (chartFrame x u y) =
    g.inner y (D.connection (chartFrame x v) y (chartFrame x u y)) (chartFrame x w y) +
      g.inner y (chartFrame x v y) (D.connection (chartFrame x w) y (chartFrame x u y)) at h
  dsimp only [D, g] at h
  rw [closedChartChristoffel_connection F T htime hy hs u v,
    closedChartChristoffel_connection F T htime hy hs u w] at h
  rw [chartActionMetric_closed_spatial_apply F T htime hy hs,
    chartActionMetric_apply F T hy s, chartActionMetric_apply F T hy s]
  exact h

theorem chartActionMetric_symm_at {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (s : ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, extChartAt (𝓡 n) x y) v w =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y) w v := by
  rw [chartActionMetric_apply F T hy s, chartActionMetric_apply F T hy s]
  exact (F.metric (T - s ^ 2)).symm y _ _

theorem variation_regularizedEulerResidual_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    (R : RegularizedLGeodesicData p) {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (W : TangentSpace (𝓡 n) (V.baseSquareCurve s)) :
    regularizedEulerResidual F T V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂)
      D.velocity_extension s W = 0 := by
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have heq : EqOn V.baseSquareCurve R.path.curve (sqrtParameterInterval τ₁ τ₂) := by
    intro r hr
    exact ((V.square_agrees r hr 0 hzero).trans (V.at_zero (r ^ 2))).trans
      (R.path.agrees r hr).symm
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have hR := ((R.path.smooth s (R.path.interval_subset hs)).contMDiffAt
    (R.path.open_domain.mem_nhds (R.path.interval_subset hs))).mdifferentiableAt (by simp)
  rw [regularizedEulerResidual_congr F T heq D.velocity_extension R.velocity_extension hs
    (hC s hs) hR]
  exact R.equation s hs W

end PoincareConjecture.M08
