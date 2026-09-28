import PoincareConjecture.Proofs.M08.ChartEulerCoefficients
import PoincareConjecture.Proofs.M08.ClosedChartCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance endpointEulerCoefficientsInstance1 : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance endpointEulerCoefficientsInstance2 : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance endpointEulerCoefficientsInstance3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance endpointEulerCoefficientsInstance4 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem bilinear_curve_hasDerivWithinAt (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    {C : Set ℝ} {Ω : Set (ℝ × E)} {u v : ℝ → E} {s : ℝ} {q a : E}
    {dG : (ℝ × E) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    (hG : HasFDerivWithinAt G dG Ω (s, u s))
    (hu : HasDerivWithinAt u q C s) (hv : HasDerivWithinAt v a C s)
    (hmap : MapsTo (fun r ↦ (r, u r)) C Ω) (z : E) :
    HasDerivWithinAt (fun r ↦ G (r, u r) (v r) z)
      (dG (1, 0) (v s) z + dG (0, q) (v s) z + G (s, u s) a z) C s := by
  have h := (((hG.comp_hasDerivWithinAt s
    (HasDerivWithinAt.prodMk (hasDerivWithinAt_id s C) hu) hmap).clm_apply hv).clm_apply
      (hasDerivWithinAt_const s C z))
  have hsplit : ((1 : ℝ), q) = (1, 0) + (0, q) := by ext <;> simp
  simpa only [Function.comp_def, id_eq, hsplit, map_add, add_apply,
    map_zero, add_zero, add_assoc] using h

end Derivative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable local instance endpointEulerCoefficientsInstance5 : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance endpointEulerCoefficientsInstance6 : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance endpointEulerCoefficientsInstance7 :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance endpointEulerCoefficientsInstance8 :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 800000 in
theorem scalarCurvature_slice_contMDiffAt_of_mem {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ∈ J) (y : M) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (F.connection t).scalarCurvature y := by
  rw [← contMDiffWithinAt_univ]
  have hi : ContMDiffWithinAt (𝓡 n) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun z : M ↦ (t, z)) univ y := contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
  exact ((hM04.scalar_regular n M J F) (t, y) ⟨ht, mem_univ y⟩).comp y hi
    (fun z _ ↦ ⟨ht, mem_univ z⟩)

set_option maxHeartbeats 800000 in
theorem chartActionMetric_closed_spatial_apply {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (z v w : EuclideanSpace ℝ (Fin n)) :
    spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x)
        (s, extChartAt (𝓡 n) x y) z v w =
      mvfderiv (𝓡 n) (fun p ↦ (F.metric (T - s ^ 2)).inner p
        (chartFrame x v p) (chartFrame x w p)) y (chartFrame x z y) := by
  let e := extChartAt (𝓡 n) x
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have htarget : e y ∈ e.target := e.map_source hy'
  have hd := hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x) _
    (chartActionMetric_closed_contDiffOn F T x htime) hs htarget
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
theorem chartActionPotential_closed_spatial_apply {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (w : EuclideanSpace ℝ (Fin n)) :
    spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionPotential F T x)
        (s, extChartAt (𝓡 n) x y) w =
      2 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature y
        (chartFrame x w y) := by
  let e := extChartAt (𝓡 n) x
  let f := (F.connection (T - s ^ 2)).scalarCurvature
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have htarget : e y ∈ e.target := e.map_source hy'
  have hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f y :=
    scalarCurvature_slice_contMDiffAt_of_mem F hM04 (htime s hs) y
  have hinv : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm (e y) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x _ htarget).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds htarget)
  have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (e.symm (e y)) := by
    rwa [e.left_inv hy']
  have hc : DifferentiableAt ℝ (f ∘ e.symm) (e y) :=
    (hf'.comp (e y) hinv).contDiffAt.differentiableAt (by simp)
  have hd := hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x) _
    (chartActionPotential_closed_contDiffOn F hM04 T x htime) hs htarget
  have heq := hd.unique (hc.hasFDerivAt.const_mul (2 * s ^ 2))
  have h := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A w) heq
  calc
    _ = 2 * s ^ 2 * fderiv ℝ (f ∘ e.symm) (e y) w := by
      simpa only [smul_apply, smul_eq_mul] using h
    _ = _ := congrArg (fun a : ℝ ↦ 2 * s ^ 2 * a)
      (chart_scalar_fderiv_apply hy f (hf.mdifferentiableAt (by simp)) w)

theorem chartActionMetric_closed_connection_diagonal {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w : EuclideanSpace ℝ (Fin n)) :
    (F.metric (T - s ^ 2)).inner y
      ((F.connection (T - s ^ 2)).connection (chartFrame x v) y (chartFrame x v y))
      (chartFrame x w y) =
      spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x y) v v w -
        spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x y) w v v / 2 := by
  rw [chartActionMetric_closed_spatial_apply F T htime hy hs,
    chartActionMetric_closed_spatial_apply F T htime hy hs,
    chartFrame_connection_diagonal _ _ hy]
  ring

theorem chartActionMetric_closed_time_derivative {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w : EuclideanSpace ℝ (Fin n)) :
    HasDerivWithinAt (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x y) v w)
      (4 * s * (F.connection (T - s ^ 2)).ricci y (chartFrame x v y) (chartFrame x w y)) C s := by
  have heq : (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x y) v w) =
      (fun r ↦ (F.metric (T - r ^ 2)).inner y (chartFrame x v y) (chartFrame x w y)) :=
    funext (fun r ↦ chartActionMetric_apply F T hy r v w)
  rw [heq]
  have hevol := F.equation (T - s ^ 2) (htime s hs) y (chartFrame x v y) (chartFrame x w y)
  have htimeDeriv : HasDerivAt (fun r : ℝ ↦ T - r ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_sub T
  convert hevol.comp s htimeDeriv.hasDerivWithinAt htime using 1 <;> first | rfl | ring

set_option maxHeartbeats 800000 in
theorem chartActionMetric_closed_curve_derivative {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (hCs : UniqueDiffWithinAt ℝ C s)
    {u : ℝ → EuclideanSpace ℝ (Fin n)} {q a : EuclideanSpace ℝ (Fin n)}
    (hu : HasDerivAt u q s) (hq : HasDerivAt (deriv u) a s)
    (hus : u s = extChartAt (𝓡 n) x y)
    (hmap : MapsTo u C (extChartAt (𝓡 n) x).target) (w : EuclideanSpace ℝ (Fin n)) :
    HasDerivWithinAt (fun r ↦ chartActionMetric F T x (r, u r) (deriv u r) w)
      (4 * s * (F.connection (T - s ^ 2)).ricci y (chartFrame x q y) (chartFrame x w y) +
        spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x y) q q w +
        chartActionMetric F T x (s, extChartAt (𝓡 n) x y) a w) C s := by
  have hdG := (((chartActionMetric_closed_contDiffOn F T x htime)
    (s, u s) ⟨hs, hmap hs⟩).differentiableWithinAt (by simp)).hasFDerivWithinAt
  let dG := fderivWithin ℝ (chartActionMetric F T x)
    (C ×ˢ (extChartAt (𝓡 n) x).target) (s, u s)
  have hcurve := bilinear_curve_hasDerivWithinAt (chartActionMetric F T x) hdG
    hu.hasDerivWithinAt hq.hasDerivWithinAt (fun r hr ↦ ⟨hr, hmap hr⟩) w
  have htime' : HasDerivWithinAt (fun r ↦ chartActionMetric F T x (r, u s) q w)
      (dG (1, 0) q w) C s := by
    have hi : HasDerivWithinAt (fun r : ℝ ↦ (r, u s)) (1, 0) C s :=
      (hasDerivWithinAt_id s C).prodMk (hasDerivWithinAt_const s C (u s))
    have hmapFixed : MapsTo (fun r : ℝ ↦ (r, u s)) C
        (C ×ˢ (extChartAt (𝓡 n) x).target) := fun r hr ↦ ⟨hr, hmap hs⟩
    have hGtime : HasDerivWithinAt (fun r ↦ chartActionMetric F T x (r, u s))
        (dG (1, 0)) C s := hdG.comp_hasDerivWithinAt (f := fun r : ℝ ↦ (r, u s)) s hi hmapFixed
    have h := ((hGtime.clm_apply (hasDerivWithinAt_const s C q)).clm_apply
          (hasDerivWithinAt_const s C w))
    simpa only [Function.comp_def, id_eq, map_zero, add_zero, add_apply] using h
  have hfixed := chartActionMetric_closed_time_derivative F T htime hy hs q w
  rw [← hus] at hfixed
  have heq := (htime'.derivWithin hCs).symm.trans (hfixed.derivWithin hCs)
  have hspace : dG (0, q) q w = spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
      (chartActionMetric F T x) (s, u s) q q w := rfl
  change HasDerivWithinAt (fun r ↦ chartActionMetric F T x (r, u r) (deriv u r) w)
    (dG (1, 0) (deriv u s) w + dG (0, q) (deriv u s) w +
      chartActionMetric F T x (s, u s) a w) C s at hcurve
  rw [hu.deriv, heq, hspace] at hcurve
  simpa only [hus] using hcurve

end PoincareConjecture.M08

