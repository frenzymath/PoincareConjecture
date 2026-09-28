import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.AdaptedCoefficient

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

local instance squareDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance squareDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance squareBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance squareBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem chartActionMetric_spatial_apply_squareDomain {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) {s : ℝ}
    (hs : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (z v w : EuclideanSpace ℝ (Fin n)) :
    spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) z v w =
      mvfderiv (𝓡 n) (fun p ↦ (F.metric (T - s ^ 2)).inner p
        (chartFrame x v p) (chartFrame x w p)) y (chartFrame x z y) := by
  let e := extChartAt (𝓡 n) x
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have htarget : e y ∈ e.target := e.map_source hy'
  have hd := hasFDerivAt_spatial (chartActionDomain_open F T x) _
    (chartActionMetric_contDiffOn F T x) ⟨hs, htarget⟩
  have heval := (hd.clm_apply (hasFDerivAt_const v (e y))).clm_apply
    (hasFDerivAt_const w (e y))
  have hevald := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A z) heval.fderiv
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] at hevald
  let f : M → ℝ := fun p ↦ (F.metric (T - s ^ 2)).inner p
    (chartFrame x v p) (chartFrame x w p)
  have heq : (fun q ↦ chartActionMetric F T x (s, q) v w) =ᶠ[𝓝 (e y)] f ∘ e.symm := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds htarget] with q hq
    have hq' : e.symm q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
      simpa only [e, extChartAt_source] using e.map_target hq
    exact metricInChart_apply (F.metric (T - s ^ 2)) hq' v w
  calc
    _ = fderiv ℝ (fun q ↦ chartActionMetric F T x (s, q) v w) (e y) z := hevald.symm
    _ = fderiv ℝ (f ∘ e.symm) (e y) z :=
      congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A z) (heq.fderiv_eq (𝕜 := ℝ))
    _ = _ := chart_scalar_fderiv_apply hy f
      ((chartFrame_inner_contMDiffAt _ hy v w).mdifferentiableAt (by simp)) z

theorem chartActionMetric_time_derivative_squareDomain {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) {s : ℝ}
    (hs : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (v w : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x y) v w)
      (4 * s * (F.connection (T - s ^ 2)).ricci y (chartFrame x v y) (chartFrame x w y)) s := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  have heq : (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x y) v w) =
      (fun r ↦ (F.metric (T - r ^ 2)).inner y (chartFrame x v y) (chartFrame x w y)) := by
    funext r
    unfold chartActionMetric
    rw [(extChartAt (𝓡 n) x).left_inv hy', metricInChart_apply _ hy]
    rfl
  rw [heq]
  have htime_mem : T - s ^ 2 ∈ J :=
    interior_subset (s := (fun r : ℝ ↦ T - r ^ 2) ⁻¹' J) hs
  have hevol := F.equation (T - s ^ 2) htime_mem y
    (chartFrame x v y) (chartFrame x w y)
  have htime : HasDerivAt (fun r : ℝ ↦ T - r ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_sub T
  have hevent : ∀ᶠ r in 𝓝 s, T - r ^ 2 ∈ J := mem_interior_iff_mem_nhds.mp hs
  convert hevol.comp_hasDerivAt s htime hevent using 1 <;> first | rfl | ring

theorem chartFrame_connection_koszul
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w u : EuclideanSpace ℝ (Fin n)) :
    2 * g.inner y (D.connection (chartFrame x w) y (chartFrame x v y))
        (chartFrame x u y) =
      mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x w p) (chartFrame x u p)) y
          (chartFrame x v y) +
        mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x u p) (chartFrame x v p)) y
          (chartFrame x w y) -
        mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x w p)) y
          (chartFrame x u y) := by
  have hfield (a : EuclideanSpace ℝ (Fin n)) :=
    ((chartFrame_contMDiffOn x a y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have h := D.koszul_identity (hfield v) (hfield w) (hfield u)
  rw [chartFrame_mlieBracket hy v w, chartFrame_mlieBracket hy w u,
    chartFrame_mlieBracket hy u v] at h
  simpa [LeviCivitaData.covariantDerivativeOnFields] using h

theorem chartConnection_pairing_eq_retainedConnection_squareDomain
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hs : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (v w u : EuclideanSpace ℝ (Fin n)) :
    (F.metric (T - s ^ 2)).inner y
        ((F.connection (T - s ^ 2)).connection (chartFrame x w) y
          (chartFrame x v y)) (chartFrame x u y) =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (chartConnection (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x y) v w) u := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  have hz : (s, extChartAt (𝓡 n) x y) ∈ chartActionDomain F T x :=
    ⟨hs, (extChartAt (𝓡 n) x).map_source hy'⟩
  have hK := chartFrame_connection_koszul (F.metric (T - s ^ 2))
    (F.connection (T - s ^ 2)) hy v w u
  rw [← chartActionMetric_spatial_apply_squareDomain F T hy hs v w u,
    ← chartActionMetric_spatial_apply_squareDomain F T hy hs w u v,
    ← chartActionMetric_spatial_apply_squareDomain F T hy hs u v w] at hK
  simp only [spatialFDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply] at hK
  have hG := (((chartActionMetric_contDiffOn F T x) _ hz).contDiffAt
    ((chartActionDomain_open F T x).mem_nhds hz)).differentiableAt (by simp)
  have hsym : ∀ᶠ q in 𝓝 (s, extChartAt (𝓡 n) x y), ∀ v w,
      chartActionMetric F T x q v w = chartActionMetric F T x q w v := by
    filter_upwards [(chartActionDomain_open F T x).mem_nhds hz] with q hq
    exact chartActionMetric_symm F T x hq
  rw [fderiv_bilinear_symm _ _ hG hsym (0, w) u v] at hK
  rw [chartConnection_pairing _ _ (chartActionMetric_pos F T x hz)]
  linarith only [hK]

theorem chartConnection_eq_retainedConnection_squareDomain
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hs : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (v w : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).connection (chartFrame x w) y (chartFrame x v y) =
      chartFrame x (chartConnection (chartActionMetric F T x)
        (s, extChartAt (𝓡 n) x y) v w) y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro z
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let u := e.continuousLinearMapAt ℝ y z
  have hu : chartFrame x u y = z := e.symmL_continuousLinearMapAt hy z
  have h := chartConnection_pairing_eq_retainedConnection_squareDomain F T s x y hy hs v w u
  rw [chartActionMetric_apply F T hy, hu] at h
  exact h

theorem chartActionMetric_time_fderiv_squareDomain
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hs : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) (1, 0) v w =
      4 * s * (F.connection (T - s ^ 2)).ricci y (chartFrame x v y) (chartFrame x w y) := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  have hz : (s, extChartAt (𝓡 n) x y) ∈ chartActionDomain F T x :=
    ⟨hs, (extChartAt (𝓡 n) x).map_source hy'⟩
  have hG := (((chartActionMetric_contDiffOn F T x) _ hz).contDiffAt
    ((chartActionDomain_open F T x).mem_nhds hz)).differentiableAt (by simp)
  have hc := hG.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s (extChartAt (𝓡 n) x y)))
  have heval := (hc.clm_apply (hasDerivAt_const s v)).clm_apply (hasDerivAt_const s w)
  have h := heval.unique (chartActionMetric_time_derivative_squareDomain F T hy hs v w)
  simpa only [Function.comp_def, map_zero, add_zero, ContinuousLinearMap.zero_apply,
    zero_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply] using h

theorem chartTransportOperator_adapted_pairing_squareDomain
    {J : Set ℝ} (F : RicciFlow n M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hs : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (a v : EuclideanSpace ℝ (Fin n)) (Z : TangentSpace (𝓡 n) y) :
    (F.metric (T - s ^ 2)).inner y
        (chartFrame x (chartTransportOperator (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x y) a v) y +
          (F.connection (T - s ^ 2)).connection (chartFrame x v) y
            (chartFrame x a y)) Z =
      -(2 * s) * (F.connection (T - s ^ 2)).ricci y (chartFrame x v y) Z := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let w := e.continuousLinearMapAt ℝ y Z
  have hw : chartFrame x w y = Z := e.symmL_continuousLinearMapAt hy Z
  rw [← hw, map_add, add_apply, ← chartActionMetric_apply F T hy,
    chartConnection_pairing_eq_retainedConnection_squareDomain F T s x y hy hs a v w]
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  have hz : (s, extChartAt (𝓡 n) x y) ∈ chartActionDomain F T x :=
    ⟨hs, (extChartAt (𝓡 n) x).map_source hy'⟩
  rw [chartTransportOperator_pairing _ _ (chartActionMetric_pos F T x hz),
    chartActionMetric_time_fderiv_squareDomain F T s x y hy hs v w]
  ring

theorem ancient_squareTime_mem_interior (s : ℝ) :
    s ∈ interior ((fun r : ℝ ↦ (0 : ℝ) - r ^ 2) ⁻¹' Iic 0) := by
  have h : ((fun r : ℝ ↦ (0 : ℝ) - r ^ 2) ⁻¹' Iic 0) = univ := by
    ext r
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    nlinarith [sq_nonneg r]
  rw [h, interior_univ]
  exact mem_univ s

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
