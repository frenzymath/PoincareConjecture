import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MetricPair
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Surface












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance traceDerivativeDualGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance traceDerivativeDualSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance traceDerivativeBilinearGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance traceDerivativeBilinearSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem parametricExtension_metric_self_contMDiffAt {J C : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn C α Y) {y : M} {s : ℝ}
    (hE : (s, y) ∈ E.domain) (ht : T - s ^ 2 ∈ interior J) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × M => (F.metric (T - z.1 ^ 2)).inner z.2
        (E.extension z.1 z.2) (E.extension z.1 z.2)) (s, y) := by
  have hmap : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun z : ℝ × M => (T - z.1 ^ 2, z.2)) (s, y) :=
    (contMDiffAt_const.sub (contMDiffAt_fst.pow 2)).prodMk contMDiffAt_snd
  have hmetric := ((F.smooth (T - s ^ 2, y) ⟨interior_subset ht, mem_univ y⟩).contMDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) univ_mem)).comp (s, y) hmap
  have hfield := (E.smooth (s, y) hE).contMDiffAt (E.open_domain.mem_nhds hE)
  have h : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : ℝ × M => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) z.2
        ((F.metric (T - z.1 ^ 2)).inner z.2
          (E.extension z.1 z.2) (E.extension z.1 z.2))) (s, y) := by
    exact ContMDiffAt.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
      hmetric hfield hfield
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffAt_totalSpace.mp h).2

private theorem parametricExtension_metric_self_time {J C : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn C α Y) {y : M} {s : ℝ}
    (hE : (s, y) ∈ E.domain) (ht : T - s ^ 2 ∈ interior J) :
    HasDerivAt (fun r => (F.metric (T - r ^ 2)).inner y
        (E.extension r y) (E.extension r y))
      (4 * s * (F.connection (T - s ^ 2)).ricci y (E.extension s y) (E.extension s y) +
        2 * (F.metric (T - s ^ 2)).inner y
          (deriv (fun r => E.extension r y) s) (E.extension s y)) s := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) y) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) y) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) y
  let v := fun r => e.continuousLinearMapAt ℝ y (E.extension r y)
  let a := e.continuousLinearMapAt ℝ y (deriv (fun r => E.extension r y) s)
  let G := fun r => chartActionMetric F T y (r, extChartAt (𝓡 n) y y)
  have hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) y).source := mem_chart_source _ y
  have hv : HasDerivAt v a s := (e.continuousLinearMapAt ℝ y).hasFDerivAt.comp_hasDerivAt s
    (parametricExtension_differentiableAt_time E hE).hasDerivAt
  have hdom : (s, extChartAt (𝓡 n) y y) ∈ chartActionDomain F T y :=
    ⟨squareTime_mem_interior_preimage ht, mem_extChartAt_target y⟩
  have hGbase := (((chartActionMetric_contDiffOn F T y) _ hdom).contDiffAt
    ((chartActionDomain_open F T y).mem_nhds hdom)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G s := hGbase.comp
    (f := fun r : ℝ => (r, extChartAt (𝓡 n) y y)) s
    (differentiableAt_id.prodMk (differentiableAt_const _))
  have heq (r : ℝ) : chartFrame y (v r) y = E.extension r y :=
    e.symmL_continuousLinearMapAt hy _
  have hea : chartFrame y a y = deriv (fun r => E.extension r y) s :=
    e.symmL_continuousLinearMapAt hy _
  have hfixed := (hG.hasDerivAt.clm_apply (hasDerivAt_const s (v s))).clm_apply
    (hasDerivAt_const s (v s))
  have hmetric := chartActionMetric_time_derivative F T hy ht (v s) (v s)
  have hdG : deriv G s (v s) (v s) =
      4 * s * (F.connection (T - s ^ 2)).ricci y (E.extension s y) (E.extension s y) := by
    simpa only [map_zero, add_zero, heq] using hfixed.unique hmetric
  have h := (hG.hasDerivAt.clm_apply hv).clm_apply hv
  have h' : HasDerivAt (fun r => (F.metric (T - r ^ 2)).inner y
      (E.extension r y) (E.extension r y))
      ((F.metric (T - s ^ 2)).inner y (E.extension s y)
          (deriv (fun r => E.extension r y) s) +
        (F.metric (T - s ^ 2)).inner y (deriv (fun r => E.extension r y) s)
          (E.extension s y) +
        4 * s * (F.connection (T - s ^ 2)).ricci y (E.extension s y) (E.extension s y)) s := by
    simpa only [add_apply, hdG, G, chartActionMetric_apply F T hy, heq, hea,
      add_assoc, add_comm, add_left_comm]
      using h
  apply h'.congr_deriv
  rw [(F.metric (T - s ^ 2)).symm y (E.extension s y)
    (deriv (fun r => E.extension r y) s)]
  ring



theorem speed_hasDerivAt {J C : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {α : ℝ → M}
    (E : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C))
    {s : ℝ} (hs : s ∈ interior C)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (ht : T - s ^ 2 ∈ interior J) :
    HasDerivAt (fun r => (F.metric (T - r ^ 2)).inner (α r)
        (curveVelocityWithin (n := n) α C r) (curveVelocityWithin (n := n) α C r))
      (2 * (F.metric (T - s ^ 2)).inner (α s)
          (pullbackCovariantDerivative F (fun r => T - r ^ 2) α
            (curveVelocityWithin (n := n) α C) C E s) (curveVelocityWithin (n := n) α C s) +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s)
          (curveVelocityWithin (n := n) α C s) (curveVelocityWithin (n := n) α C s)) s := by
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  let A := curveVelocityWithin (n := n) α C s
  have hsC : s ∈ C := interior_subset hs
  have hC : C ∈ 𝓝 s := mem_interior_iff_mem_nhds.mp hs
  have hvel : curveVelocity (n := n) α s = A := by
    simp only [A, curveVelocityWithin, curveVelocity, mfderivWithin_of_mem_nhds hC]
  have hspace : mvfderiv (𝓡 n)
      (fun y => g.inner y (E.extension s y) (E.extension s y)) (α s) A =
      2 * g.inner (α s) (D.connection (E.extension s) (α s) A) (E.extension s (α s)) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hEs := (parametricExtension_contMDiffAt_space E (E.graph_mem s hsC)).mdifferentiableAt
      (by simp)
    have h := D.metricCompatible.mvfderiv_inner_eq
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) A) hEs hEs
    change mvfderiv (𝓡 n)
        (fun y => g.inner y (E.extension s y) (E.extension s y)) (α s)
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) A (α s)) =
      g.inner (α s) (D.connection (E.extension s) (α s)
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) A (α s))) (E.extension s (α s)) +
        g.inner (α s) (E.extension s (α s))
          (D.connection (E.extension s) (α s)
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) A (α s))) at h
    simp only [FiberBundle.extend_apply_self] at h
    rw [g.symm (α s) (E.extension s (α s)) (D.connection (E.extension s) (α s) A)] at h
    linarith only [h]
  have htime := parametricExtension_metric_self_time F T E (E.graph_mem s hsC) ht
  have h := scalar_graph_hasDerivAt _
    ((parametricExtension_metric_self_contMDiffAt F T E (E.graph_mem s hsC) ht).mdifferentiableAt
      (by simp)) hα
  rw [htime.deriv, hvel, hspace, E.agrees s hsC] at h
  have h' := h.congr_of_eventuallyEq (show (fun r => (F.metric (T - r ^ 2)).inner (α r)
      (curveVelocityWithin (n := n) α C r) (curveVelocityWithin (n := n) α C r)) =ᶠ[𝓝 s]
        (fun r => (F.metric (T - r ^ 2)).inner (α r)
          (E.extension r (α r)) (E.extension r (α r))) from by
    filter_upwards [hC] with r hr
    rw [E.agrees r hr])
  apply h'.congr_deriv
  simp only [pullbackCovariantDerivative, map_add, add_apply, g, D, A]
  ring



theorem speed_hasDerivAt_of_regularizedEuler {J C : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) {α : ℝ → M}
    (E : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C))
    {s : ℝ} (hs : s ∈ interior C)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (ht : T - s ^ 2 ∈ interior J)
    (heuler : regularizedLGeodesicEquation F T α C E s) :
    HasDerivAt (fun r => (F.metric (T - r ^ 2)).inner (α r)
        (curveVelocityWithin (n := n) α C r) (curveVelocityWithin (n := n) α C r))
      (-4 * s * (F.connection (T - s ^ 2)).ricci (α s)
          (curveVelocityWithin (n := n) α C s) (curveVelocityWithin (n := n) α C s) +
        4 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature (α s)
          (curveVelocityWithin (n := n) α C s)) s := by
  have h := speed_hasDerivAt F T E hs hα ht
  have hE := heuler (curveVelocityWithin (n := n) α C s)
  unfold regularizedEulerResidual scalarCurvatureDifferential at hE
  exact h.congr_deriv (by linarith only [hE])

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}



theorem surface_scaled_index_trace (D : LeviCivitaData g) (x : M)
    (A : TangentSpace (𝓡 2) x) (s : ℝ) {c : ℝ} (hc : c ≠ 0)
    (e : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    c ^ 2 * (∑ i, (g.inner x ((1 / c - s * (s / c) * D.scalarCurvature x) • e i)
        ((1 / c - s * (s / c) * D.scalarCurvature x) • e i) +
      D.curvatureTensor x ((s / c) • e i) A A ((s / c) • e i) +
      2 * s ^ 2 * D.hessian D.scalarCurvature x ((s / c) • e i) ((s / c) • e i) -
      4 * s * ricciDerivativePairing D x ((s / c) • e i) A ((s / c) • e i) +
      2 * s * ricciDerivativePairing D x A ((s / c) • e i) ((s / c) • e i))) =
      2 - 4 * s ^ 2 * D.scalarCurvature x +
        2 * s ^ 4 * (D.laplacian D.scalarCurvature x + D.scalarCurvature x ^ 2) -
        s ^ 2 * D.ricci x A A := by
  rw [D.sum_surface_indexDensity x A s (s / c) (1 / c) e]
  field_simp [hc] <;> ring

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variation.Geometry

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem hasDerivAt_scalarCurvature_square_curve_within (K : AncientKappaSolution 2 M)
    {C : Set ℝ} {α : ℝ → M} {s : ℝ} (hs : s ∈ interior C) (hs0 : s ≠ 0)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 2) α s) :
    HasDerivAt (fun r => (K.flow.connection (-(r ^ 2))).scalarCurvature (α r))
      (-2 * s * ((K.flow.connection (-(s ^ 2))).laplacian
        (K.flow.connection (-(s ^ 2))).scalarCurvature (α s) +
          (K.flow.connection (-(s ^ 2))).scalarCurvature (α s) ^ 2) +
        mvfderiv (𝓡 2) (K.flow.connection (-(s ^ 2))).scalarCurvature (α s)
          (curveVelocityWithin (n := 2) α C s)) s := by
  simpa only [curveVelocityWithin, curveVelocity,
    mfderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hs)] using
    K.hasDerivAt_scalarCurvature_square_curve hs0 hα

theorem hasDerivAt_speed_square_curve_of_euler (K : AncientKappaSolution 2 M)
    {C : Set ℝ} {α : ℝ → M}
    (E : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := 2) α C))
    {s : ℝ} (hs : s ∈ interior C) (hs0 : s ≠ 0)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 2) α s)
    (heuler : regularizedLGeodesicEquation K.flow 0 α C E s) :
    HasDerivAt (fun r => (K.flow.metric (-(r ^ 2))).inner (α r)
        (curveVelocityWithin (n := 2) α C r) (curveVelocityWithin (n := 2) α C r))
      (-4 * s * (K.flow.connection (-(s ^ 2))).ricci (α s)
          (curveVelocityWithin (n := 2) α C s) (curveVelocityWithin (n := 2) α C s) +
        4 * s ^ 2 * mvfderiv (𝓡 2) (K.flow.connection (-(s ^ 2))).scalarCurvature (α s)
          (curveVelocityWithin (n := 2) α C s)) s := by
  have ht : (0 : ℝ) - s ^ 2 ∈ interior (Iic (0 : ℝ)) := by
    rw [interior_Iic]
    change (0 : ℝ) - s ^ 2 < 0
    rw [zero_sub]
    exact neg_lt_zero.mpr (sq_pos_of_ne_zero hs0)
  have h := speed_hasDerivAt_of_regularizedEuler K.flow 0 E hs hα ht heuler
  simp_rw [zero_sub] at h
  apply h.congr_deriv
  have hRic := congrArg (fun t : ℝ => (K.flow.connection t).ricci (α s)
    (curveVelocityWithin (n := 2) α C s) (curveVelocityWithin (n := 2) α C s))
      (zero_sub (s ^ 2))
  have hR := congrArg (fun t : ℝ =>
    mvfderiv (𝓡 2) (K.flow.connection t).scalarCurvature (α s)
      (curveVelocityWithin (n := 2) α C s)) (zero_sub (s ^ 2))
  rw [hRic, hR]

end PoincareConjecture.AncientKappaSolution
