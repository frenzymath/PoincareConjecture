import PoincareConjecture.Proofs.M08.ChartEulerFrame
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance chartEulerCoefficientsInstance1 : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance chartEulerCoefficientsInstance2 : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance chartEulerCoefficientsInstance3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance chartEulerCoefficientsInstance4 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem bilinear_curve_hasDerivAt (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    {u v : ℝ → E} {s : ℝ} {q a : E}
    {dG : (ℝ × E) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    (hG : HasFDerivAt G dG (s, u s)) (hu : HasDerivAt u q s) (hv : HasDerivAt v a s)
    (z : E) :
    HasDerivAt (fun r ↦ G (r, u r) (v r) z)
      (dG (1, 0) (v s) z + dG (0, q) (v s) z + G (s, u s) a z) s := by
  have h := (((hG.comp_hasDerivAt s (HasDerivAt.prodMk (hasDerivAt_id s) hu)).clm_apply hv).clm_apply
    (hasDerivAt_const s z))
  have hsplit : ((1 : ℝ), q) = (1, 0) + (0, q) := by ext <;> simp
  simpa only [Function.comp_def, id_eq, hsplit, map_add, ContinuousLinearMap.add_apply,
    map_zero, add_zero, add_assoc] using h

end Derivative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable local instance chartEulerCoefficientsInstance5 : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance chartEulerCoefficientsInstance6 : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance chartEulerCoefficientsInstance7 :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance chartEulerCoefficientsInstance8 :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem chartActionMetric_apply {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (s : ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, extChartAt (𝓡 n) x y) v w =
      (F.metric (T - s ^ 2)).inner y (chartFrame x v y) (chartFrame x w y) := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  unfold chartActionMetric
  rw [(extChartAt (𝓡 n) x).left_inv hy']
  exact metricInChart_apply _ hy v w

theorem chartFrame_inner_contMDiffAt (g : RiemannianMetric n M) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x w p)) y := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  exact ((chartFrame_contMDiffOn x v y hy).contMDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).inner_bundle
      ((chartFrame_contMDiffOn x w y hy).contMDiffAt
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy))

set_option maxHeartbeats 800000 in
theorem chartActionMetric_spatial_apply {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (ht : T - s ^ 2 ∈ interior J) (z v w : EuclideanSpace ℝ (Fin n)) :
    spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) z v w =
      mvfderiv (𝓡 n) (fun p ↦ (F.metric (T - s ^ 2)).inner p
        (chartFrame x v p) (chartFrame x w p)) y (chartFrame x z y) := by
  let e := extChartAt (𝓡 n) x
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have htarget : e y ∈ e.target := e.map_source hy'
  have hd := hasFDerivAt_spatial (chartActionDomain_open F T x) _
    (chartActionMetric_contDiffOn F T x) ⟨ht, htarget⟩
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

theorem scalarCurvature_slice_contMDiffAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ∈ interior J) (y : M) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (F.connection t).scalarCurvature y := by
  have h := ((hM04.scalar_regular n M J F) (t, y) ⟨interior_subset ht, mem_univ y⟩).contMDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) univ_mem)
  exact h.comp y (contMDiffAt_const.prodMk contMDiffAt_id)

set_option maxHeartbeats 800000 in
theorem chartActionPotential_spatial_apply {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (ht : T - s ^ 2 ∈ interior J) (w : EuclideanSpace ℝ (Fin n)) :
    spatialFDeriv (chartActionPotential F T x) (s, extChartAt (𝓡 n) x y) w =
      2 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature y
        (chartFrame x w y) := by
  let e := extChartAt (𝓡 n) x
  let f := (F.connection (T - s ^ 2)).scalarCurvature
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have htarget : e y ∈ e.target := e.map_source hy'
  have hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f y :=
    scalarCurvature_slice_contMDiffAt F hM04 ht y
  have hinv : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm (e y) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x _ htarget).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds htarget)
  have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (e.symm (e y)) := by
    rwa [e.left_inv hy']
  have hc : DifferentiableAt ℝ (f ∘ e.symm) (e y) :=
    (hf'.comp (e y) hinv).contDiffAt.differentiableAt (by simp)
  have hd := hasFDerivAt_spatial (chartActionDomain_open F T x) _
    (chartActionPotential_contDiffOn F hM04 T x) ⟨ht, htarget⟩
  have heq := hd.unique (hc.hasFDerivAt.const_mul (2 * s ^ 2))
  have h := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A w) heq
  change spatialFDeriv (chartActionPotential F T x) (s, e y) w =
    2 * s ^ 2 * mvfderiv (𝓡 n) f y (chartFrame x w y)
  calc
    _ = 2 * s ^ 2 * fderiv ℝ (f ∘ e.symm) (e y) w := by
      simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
    _ = _ := congrArg (fun a : ℝ ↦ 2 * s ^ 2 * a)
      (chart_scalar_fderiv_apply hy f (hf.mdifferentiableAt (by simp)) w)

theorem chartActionMetric_connection_diagonal {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (ht : T - s ^ 2 ∈ interior J) (v w : EuclideanSpace ℝ (Fin n)) :
    (F.metric (T - s ^ 2)).inner y
      ((F.connection (T - s ^ 2)).connection (chartFrame x v) y (chartFrame x v y))
      (chartFrame x w y) =
      spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) v v w -
        spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) w v v / 2 := by
  rw [chartActionMetric_spatial_apply F T hy ht, chartActionMetric_spatial_apply F T hy ht,
    chartFrame_connection_diagonal _ _ hy]
  ring

set_option maxHeartbeats 800000 in
theorem chartActionMetric_curve_derivative {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (ht : T - s ^ 2 ∈ interior J) {u : ℝ → EuclideanSpace ℝ (Fin n)}
    {q a : EuclideanSpace ℝ (Fin n)} (hu : HasDerivAt u q s)
    (hq : HasDerivAt (deriv u) a s) (hus : u s = extChartAt (𝓡 n) x y)
    (w : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun r ↦ chartActionMetric F T x (r, u r) (deriv u r) w)
      (4 * s * (F.connection (T - s ^ 2)).ricci y (chartFrame x q y) (chartFrame x w y) +
        spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) q q w +
        chartActionMetric F T x (s, extChartAt (𝓡 n) x y) a w) s := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  have hdom : (s, u s) ∈ chartActionDomain F T x := by
    rw [hus]
    exact ⟨ht, (extChartAt (𝓡 n) x).map_source hy'⟩
  have hG := (((chartActionMetric_contDiffOn F T x) (s, u s) hdom).contDiffAt
    ((chartActionDomain_open F T x).mem_nhds hdom)).differentiableAt (by simp)
  let dG := fderiv ℝ (chartActionMetric F T x) (s, u s)
  have hdG : HasFDerivAt (chartActionMetric F T x) dG (s, u s) := hG.hasFDerivAt
  have hcurve := bilinear_curve_hasDerivAt (chartActionMetric F T x) hdG hu hq w
  have htime : HasDerivAt (fun r ↦ chartActionMetric F T x (r, u s) q w)
      (dG (1, 0) q w) s := by
    have h := (((hdG.comp_hasDerivAt s
      (HasDerivAt.prodMk (hasDerivAt_id s) (hasDerivAt_const s (u s)))).clm_apply
        (hasDerivAt_const s q)).clm_apply (hasDerivAt_const s w))
    simpa only [Function.comp_def, id_eq, map_zero, add_zero, ContinuousLinearMap.add_apply] using h
  have htime' := chartActionMetric_time_derivative F T hy ht q w
  rw [← hus] at htime'
  have heq := htime.unique htime'
  have hspace : dG (0, q) q w = spatialFDeriv (chartActionMetric F T x) (s, u s) q q w := rfl
  simpa only [hu.deriv, heq, hspace, hus] using hcurve

end PoincareConjecture.M08
