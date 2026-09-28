import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.GeometricConnection









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local instance adaptedDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance adaptedDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance adaptedBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance adaptedBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



theorem chartConnection_eq_retainedConnection
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (v w : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).connection (chartFrame x w) y (chartFrame x v y) =
      chartFrame x (chartConnection (chartActionMetric F T x)
        (s, extChartAt (𝓡 n) x y) v w) y := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro z
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let u := e.continuousLinearMapAt ℝ y z
  have hu : chartFrame x u y = z := e.symmL_continuousLinearMapAt hy z
  have h := chartConnection_pairing_eq_retainedConnection F T s x y hy ht v w u
  rw [chartActionMetric_apply F T hy, hu] at h
  exact h

theorem chartActionMetric_time_fderiv
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) (1, 0) v w =
      4 * s * (F.connection (T - s ^ 2)).ricci y (chartFrame x v y) (chartFrame x w y) := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by
    simpa only [extChartAt_source] using hy
  have hz : (s, extChartAt (𝓡 n) x y) ∈ chartActionDomain F T x :=
    ⟨squareTime_mem_interior_preimage ht, (extChartAt (𝓡 n) x).map_source hy'⟩
  have hG := (((chartActionMetric_contDiffOn F T x) _ hz).contDiffAt
    ((chartActionDomain_open F T x).mem_nhds hz)).differentiableAt (by simp)
  have hc := hG.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s (extChartAt (𝓡 n) x y)))
  have heval := (hc.clm_apply (hasDerivAt_const s v)).clm_apply (hasDerivAt_const s w)
  have h := heval.unique (chartActionMetric_time_derivative F T hy ht v w)
  simpa only [Function.comp_def, map_zero, add_zero,
    ContinuousLinearMap.zero_apply, zero_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply] using h



theorem chartTransportOperator_retainedConnection_pairing
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (a v w : EuclideanSpace ℝ (Fin n)) :
    (F.metric (T - s ^ 2)).inner y
        (chartFrame x (chartTransportOperator (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x y) a v) y) (chartFrame x w y) +
      (F.metric (T - s ^ 2)).inner y
        ((F.connection (T - s ^ 2)).connection (chartFrame x v) y
          (chartFrame x a y)) (chartFrame x w y) =
      -(2 * s) * (F.connection (T - s ^ 2)).ricci y
        (chartFrame x v y) (chartFrame x w y) := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by
    simpa only [extChartAt_source] using hy
  have hz : (s, extChartAt (𝓡 n) x y) ∈ chartActionDomain F T x :=
    ⟨squareTime_mem_interior_preimage ht, (extChartAt (𝓡 n) x).map_source hy'⟩
  rw [← chartActionMetric_apply F T hy,
    chartConnection_pairing_eq_retainedConnection F T s x y hy ht a v w,
    chartTransportOperator_pairing _ _ (chartActionMetric_pos F T x hz),
    chartActionMetric_time_fderiv F T s x y hy ht v w]
  ring



theorem chartTransportOperator_adapted_pairing
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (a v : EuclideanSpace ℝ (Fin n))
    (Z : TangentSpace (𝓡 n) y) :
    (F.metric (T - s ^ 2)).inner y
        (chartFrame x (chartTransportOperator (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x y) a v) y +
          (F.connection (T - s ^ 2)).connection (chartFrame x v) y
            (chartFrame x a y)) Z =
      -(2 * s) * (F.connection (T - s ^ 2)).ricci y (chartFrame x v y) Z := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let w := e.continuousLinearMapAt ℝ y Z
  have hw : chartFrame x w y = Z := e.symmL_continuousLinearMapAt hy Z
  have h := chartTransportOperator_retainedConnection_pairing F T s x y hy ht a v w
  rw [hw] at h
  simpa only [map_add, add_apply] using h

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
