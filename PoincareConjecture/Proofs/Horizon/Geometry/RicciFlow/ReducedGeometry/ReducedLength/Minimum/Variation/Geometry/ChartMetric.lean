import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartFrame
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import Mathlib.Analysis.Calculus.Deriv.Prod









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

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
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
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
    (chartActionMetric_contDiffOn F T x) ⟨squareTime_mem_interior_preimage ht, htarget⟩
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

set_option maxHeartbeats 800000 in
theorem chartActionPotential_spatial_apply {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ)
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2))
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
    (F.connection (T - s ^ 2)).contMDiff_scalarCurvature.contMDiffAt
  have hinv : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm (e y) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x _ htarget).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds htarget)
  have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (e.symm (e y)) := by
    rwa [e.left_inv hy']
  have hc : DifferentiableAt ℝ (f ∘ e.symm) (e y) :=
    (hf'.comp (e y) hinv).contDiffAt.differentiableAt (by simp)
  have hd := hasFDerivAt_spatial (chartActionDomain_open F T x) _
    (chartActionPotential_contDiffOn F T hpotential x) ⟨squareTime_mem_interior_preimage ht, htarget⟩
  have heq := hd.unique (hc.hasFDerivAt.const_mul (2 * s ^ 2))
  have h := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A w) heq
  change spatialFDeriv (chartActionPotential F T x) (s, e y) w =
    2 * s ^ 2 * mvfderiv (𝓡 n) f y (chartFrame x w y)
  calc
    _ = 2 * s ^ 2 * fderiv ℝ (f ∘ e.symm) (e y) w := by
      simpa only [smul_apply, smul_eq_mul] using h
    _ = _ := congrArg (fun a : ℝ ↦ 2 * s ^ 2 * a)
      (chart_scalar_fderiv_apply hy f (hf.mdifferentiableAt (by simp)) w)

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
