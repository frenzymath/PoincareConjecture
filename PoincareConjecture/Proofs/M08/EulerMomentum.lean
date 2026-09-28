import PoincareConjecture.Proofs.M08.ChartEulerCoefficients
import PoincareConjecture.Proofs.M08.BackwardEulerTransport
import PoincareConjecture.Proofs.M08.ChartStationarity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem scalar_graph_hasDerivAt (H : ℝ × M → ℝ) {α : ℝ → M} {s : ℝ}
    (hH : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) H (s, α s))
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    HasDerivAt (fun r ↦ H (r, α r))
      (deriv (fun r ↦ H (r, α s)) s +
        mvfderiv (𝓡 n) (fun y ↦ H (s, y)) (α s) (curveVelocity (n := n) α s)) s := by
  have hgraph := mdifferentiableAt_id.prodMk hα
  have hcomp := (hH.comp s hgraph).differentiableAt.hasDerivAt
  have h := mfderiv_comp_apply s hH hgraph (1 : ℝ)
  rw [mfderiv_prodMk mdifferentiableAt_id hα, mfderiv_id] at h
  change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r ↦ H (r, α r)) s 1 =
    mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) H (s, α s)
      (1, curveVelocity (n := n) α s) at h
  rw [mfderiv_prod_eq_add_apply hH] at h
  have hscalar (f : ℝ → ℝ) : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) f s 1 = deriv f s := by
    have hf := congrArg (fun A : ℝ →L[ℝ] ℝ ↦ A 1)
      (mfderiv_eq_fderiv (𝕜 := ℝ) (f := f) (x := s))
    exact hf.trans fderiv_apply_one_eq_deriv
  dsimp only [Prod.fst, Prod.snd] at h
  rw [hscalar, hscalar] at h
  convert hcomp using 1 <;> first | rfl | exact h.symm

section Bilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance eulerMomentumInstance1 : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance eulerMomentumInstance2 : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance eulerMomentumInstance3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance eulerMomentumInstance4 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem bilinear_moving_vector_hasDerivAt {G : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {v : ℝ → E} {s d : ℝ} {a : E} (w : E)
    (hG : DifferentiableAt ℝ G s) (hv : HasDerivAt v a s)
    (hfixed : HasDerivAt (fun r ↦ G r (v s) w) d s) :
    HasDerivAt (fun r ↦ G r (v r) w) (d + G s a w) s := by
  have h₁ := (hG.hasDerivAt.clm_apply (hasDerivAt_const s (v s))).clm_apply
    (hasDerivAt_const s w)
  have hd : deriv G s (v s) w = d := by
    simpa only [map_zero, add_zero] using h₁.unique hfixed
  have h₂ := (hG.hasDerivAt.clm_apply hv).clm_apply (hasDerivAt_const s w)
  simpa only [ContinuousLinearMap.add_apply, map_zero, add_zero, hd] using h₂

end Bilinear

noncomputable local instance eulerMomentumInstance5 : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance eulerMomentumInstance6 : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance eulerMomentumInstance7 :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance eulerMomentumInstance8 :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem parametricExtension_chart_contMDiffAt {I : Set ℝ} {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn I α Y) {x y : M} {s : ℝ}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hE : (s, y) ∈ E.domain) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) ∞
      (fun z : ℝ × M ↦
        (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt
          ℝ z.2 (E.extension z.1 z.2)) (s, y) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have h := (e.contMDiffAt_iff (x₀ := (s, y)) (f := fun z : ℝ × M ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) z.2 (E.extension z.1 z.2))
      (e.mem_source.mpr hy)).mp
    ((E.smooth _ hE).contMDiffAt (E.open_domain.mem_nhds hE))
  apply h.2.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt (e.open_baseSet.mem_nhds hy)] with z hz
  exact e.continuousLinearMapAt_apply_of_mem ℝ hz _

set_option synthInstance.maxHeartbeats 200000 in
theorem parametricExtension_metric_pair_contMDiffAt {J I : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {α : ℝ → M} {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn I α Y) {x y : M} {s : ℝ}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hE : (s, y) ∈ E.domain) (ht : T - s ^ 2 ∈ interior J)
    (w : EuclideanSpace ℝ (Fin n)) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × M ↦ (F.metric (T - z.1 ^ 2)).inner z.2
        (E.extension z.1 z.2) (chartFrame x w z.2)) (s, y) := by
  have hmap : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ (T - z.1 ^ 2, z.2)) (s, y) :=
    (contMDiffAt_const.sub (contMDiffAt_fst.pow 2)).prodMk contMDiffAt_snd
  have hmetric := ((F.smooth (T - s ^ 2, y) ⟨interior_subset ht, mem_univ y⟩).contMDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) univ_mem)).comp (s, y) hmap
  have hfield := (E.smooth (s, y) hE).contMDiffAt (E.open_domain.mem_nhds hE)
  have hframe : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) z.2
        (chartFrame x w z.2)) (s, y) :=
    ((chartFrame_contMDiffOn x w y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).comp (s, y)
        contMDiffAt_snd
  have h : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) z.2
        ((F.metric (T - z.1 ^ 2)).inner z.2
          (E.extension z.1 z.2) (chartFrame x w z.2))) (s, y) := by
    apply ContMDiffAt.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    · exact hmetric
    · exact hfield
    · exact hframe
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffAt_totalSpace.mp h).2

theorem parametricExtension_metric_pair_time {J I : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {α : ℝ → M} {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn I α Y) {x y : M} {s : ℝ}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hE : (s, y) ∈ E.domain) (ht : T - s ^ 2 ∈ interior J)
    (w : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun r ↦ (F.metric (T - r ^ 2)).inner y
        (E.extension r y) (chartFrame x w y))
      (4 * s * (F.connection (T - s ^ 2)).ricci y (E.extension s y) (chartFrame x w y) +
        (F.metric (T - s ^ 2)).inner y
          (deriv (fun r ↦ E.extension r y) s) (chartFrame x w y)) s := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) y) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) y) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let v := fun r ↦ e.continuousLinearMapAt ℝ y (E.extension r y)
  let a := e.continuousLinearMapAt ℝ y (deriv (fun r ↦ E.extension r y) s)
  have hv : HasDerivAt v a s := (e.continuousLinearMapAt ℝ y).hasFDerivAt.comp_hasDerivAt s
    (parametricExtension_differentiableAt_time E hE).hasDerivAt
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  have hdom : (s, extChartAt (𝓡 n) x y) ∈ chartActionDomain F T x :=
    ⟨ht, (extChartAt (𝓡 n) x).map_source hy'⟩
  have hG : DifferentiableAt ℝ (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) :=
    (((chartActionMetric_contDiffOn F T x) _ hdom).contDiffAt
      ((chartActionDomain_open F T x).mem_nhds hdom)).differentiableAt (by simp)
  have hGt := hG.comp (f := fun r : ℝ ↦ (r, extChartAt (𝓡 n) x y)) s
    (differentiableAt_id.prodMk (differentiableAt_const _))
  have hfixed := chartActionMetric_time_derivative F T hy ht (v s) w
  have h := bilinear_moving_vector_hasDerivAt w hGt hv hfixed
  have heq (r : ℝ) : chartFrame x (v r) y = E.extension r y :=
    e.symmL_continuousLinearMapAt hy _
  have hea : chartFrame x a y = deriv (fun r ↦ E.extension r y) s :=
    e.symmL_continuousLinearMapAt hy _
  simpa only [Function.comp_apply, chartActionMetric_apply F T hy, heq, hea] using h

theorem chartFrame_connection_cross (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.inner y (chartFrame x v y) (D.connection (chartFrame x w) y (chartFrame x v y)) =
      mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x v p)) y
        (chartFrame x w y) / 2 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdiff (z : EuclideanSpace ℝ (Fin n)) :=
    ((chartFrame_contMDiffOn x z y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt
        (by simp)
  have hcross : D.connection (chartFrame x w) y (chartFrame x v y) =
      D.connection (chartFrame x v) y (chartFrame x w y) := by
    have h := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero (hdiff v) (hdiff w)
    rw [chartFrame_mlieBracket hy v w] at h
    exact sub_eq_zero.mp h
  have h := D.metricCompatible.mvfderiv_inner_eq (chartFrame x w) (hdiff v) (hdiff v)
  change mvfderiv (𝓡 n) (fun p ↦ g.inner p (chartFrame x v p) (chartFrame x v p)) y
      (chartFrame x w y) =
      g.inner y (D.connection (chartFrame x v) y (chartFrame x w y)) (chartFrame x v y) +
      g.inner y (chartFrame x v y) (D.connection (chartFrame x v) y (chartFrame x w y)) at h
  rw [g.symm y (D.connection (chartFrame x v) y (chartFrame x w y)) (chartFrame x v y)] at h
  rw [hcross]
  linarith

set_option maxHeartbeats 800000 in
theorem parametricExtension_metric_pair_graph {J I : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (hI : IsOpen I) {α : ℝ → M}
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I))
    {x : M} {s : ℝ} (hs : s ∈ I)
    (hy : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (ht : T - s ^ 2 ∈ interior J) (w : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun r ↦ (F.metric (T - r ^ 2)).inner (α r)
        (E.extension r (α r)) (chartFrame x w (α r)))
      ((F.metric (T - s ^ 2)).inner (α s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
            (curveVelocityWithin (n := n) α I) I E s) (chartFrame x w (α s)) +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s)
          (curveVelocityWithin (n := n) α I s) (chartFrame x w (α s)) +
        spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (α s))
          w (deriv ((extChartAt (𝓡 n) x) ∘ α) s)
            (deriv ((extChartAt (𝓡 n) x) ∘ α) s) / 2) s := by
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let v := deriv ((extChartAt (𝓡 n) x) ∘ α) s
  have hvel : chartFrame x v (α s) = curveVelocityWithin (n := n) α I s := by
    rw [show curveVelocityWithin (n := n) α I s = curveVelocity (n := n) α s by
      simp only [curveVelocityWithin, curveVelocity, mfderivWithin_of_mem_nhds (hI.mem_nhds hs)]]
    unfold v chartFrame
    rw [chart_deriv_eq_velocity hy hα]
    exact Bundle.Trivialization.symmL_continuousLinearMapAt
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) hy _
  have hvel' : curveVelocity (n := n) α s = chartFrame x v (α s) := by
    rw [hvel]
    simp only [curveVelocityWithin, curveVelocity, mfderivWithin_of_mem_nhds (hI.mem_nhds hs)]
  have hE := (parametricExtension_contMDiffAt_space E (E.graph_mem s hs)).mdifferentiableAt
    (by simp)
  have hw := ((chartFrame_contMDiffOn x w (α s) hy).contMDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have hspace := D.metricCompatible.mvfderiv_inner_eq (chartFrame x v) hE hw
  change mvfderiv (𝓡 n) (fun y ↦ g.inner y (E.extension s y) (chartFrame x w y)) (α s)
      (chartFrame x v (α s)) =
      g.inner (α s) (D.connection (E.extension s) (α s) (chartFrame x v (α s)))
        (chartFrame x w (α s)) +
      g.inner (α s) (E.extension s (α s))
        (D.connection (chartFrame x w) (α s) (chartFrame x v (α s))) at hspace
  rw [E.agrees s hs, ← hvel, chartFrame_connection_cross g D hy v w,
    ← chartActionMetric_spatial_apply F T hy ht w v v] at hspace
  have htime := parametricExtension_metric_pair_time F T E hy (E.graph_mem s hs) ht w
  have h := scalar_graph_hasDerivAt _
    ((parametricExtension_metric_pair_contMDiffAt F T E hy (E.graph_mem s hs) ht w).mdifferentiableAt
      (by simp)) hα
  rw [htime.deriv, hvel', hspace, E.agrees s hs, hvel] at h
  convert h using 1
  unfold pullbackCovariantDerivative
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

set_option maxHeartbeats 1000000 in
theorem regularized_equation_chart_momentum {J I : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hI : IsOpen I)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α I)
    (hsrc : MapsTo α I (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I))
    {s : ℝ} (hs : s ∈ I) (ht : T - s ^ 2 ∈ interior J)
    (heuler : regularizedLGeodesicEquation F T α I E s) :
    HasDerivAt (fun r ↦ chartMomentumVector
        (chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) r))
      (chartForceVector
        (spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (α s)))
        (spatialFDeriv (chartActionPotential F T x) (s, extChartAt (𝓡 n) x (α s)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) s)) s := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let u := (extChartAt (𝓡 n) x) ∘ α
  let q := deriv u
  let c := fun r ↦ e.continuousLinearMapAt ℝ (α r) (E.extension r (α r))
  let G := fun r ↦ chartActionMetric F T x (r, u r)
  let P := fun r ↦ chartMomentumVector (G r) (q r)
  let Q := chartForceVector (spatialFDeriv (chartActionMetric F T x) (s, u s))
    (spatialFDeriv (chartActionPotential F T x) (s, u s)) (q s)
  have hαd (r : ℝ) (hr : r ∈ I) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α r :=
    ((hα r hr).contMDiffAt (hI.mem_nhds hr)).mdifferentiableAt one_ne_zero
  have hud : DifferentiableAt ℝ u s :=
    (((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) (hsrc hs)).mdifferentiableAt
      (by simp)).comp s (hαd s hs)).differentiableAt
  have hq (r : ℝ) (hr : r ∈ I) : q r = c r := by
    dsimp only [q, u, c]
    rw [E.agrees r hr]
    simp only [curveVelocityWithin, mfderivWithin_of_mem_nhds (hI.mem_nhds hr)]
    exact chart_deriv_eq_velocity (hsrc hr) (hαd r hr)
  have hcoord := (parametricExtension_chart_contMDiffAt E (hsrc hs)
    (E.graph_mem s hs)).mdifferentiableAt (by simp)
  have hcd : DifferentiableAt ℝ c s := by
    have h := hcoord.comp (f := fun r : ℝ ↦ (r, α r)) s
      (mdifferentiableAt_id.prodMk (hαd s hs))
    exact h.differentiableAt
  have hdom : (s, u s) ∈ chartActionDomain F T x := by
    refine ⟨ht, (extChartAt (𝓡 n) x).map_source ?_⟩
    simpa only [extChartAt_source] using hsrc hs
  have hGbase : DifferentiableAt ℝ (chartActionMetric F T x) (s, u s) :=
    (((chartActionMetric_contDiffOn F T x) _ hdom).contDiffAt
      ((chartActionDomain_open F T x).mem_nhds hdom)).differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G s := by
    have h := hGbase.comp (f := fun r : ℝ ↦ (r, u r)) s
      (differentiableAt_id.prodMk hud)
    exact h
  have hPc : DifferentiableAt ℝ (fun r ↦ chartMomentumVector (G r) (c r)) s :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.differentiableAt.comp
      s (hGd.clm_apply hcd)
  have hPd : DifferentiableAt ℝ P s := hPc.congr_of_eventuallyEq (by
    filter_upwards [hI.mem_nhds hs] with r hr
    exact congrArg (chartMomentumVector (G r)) (hq r hr))
  have hderiv : deriv P s = Q := by
    apply ext_inner_left ℝ
    intro w
    have hpair := (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt s hPd.hasDerivAt
    have hgraph := parametricExtension_metric_pair_graph F T hI E hs (hsrc hs)
      (hαd s hs) ht w
    have hnear : (fun r ↦ inner ℝ w (P r)) =ᶠ[𝓝 s]
        (fun r ↦ (F.metric (T - r ^ 2)).inner (α r)
          (E.extension r (α r)) (chartFrame x w (α r))) := by
      filter_upwards [hI.mem_nhds hs] with r hr
      dsimp only [P, G, u, Function.comp_apply]
      rw [chartMomentumVector_inner, chartActionMetric_apply F T (hsrc hr), hq r hr]
      dsimp only [c, chartFrame]
      rw [e.symmL_continuousLinearMapAt (hsrc hr)]
    have hQ : (F.metric (T - s ^ 2)).inner (α s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
            (curveVelocityWithin (n := n) α I) I E s) (chartFrame x w (α s)) +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s)
          (curveVelocityWithin (n := n) α I s) (chartFrame x w (α s)) +
        spatialFDeriv (chartActionMetric F T x) (s, u s) w (q s) (q s) / 2 =
        inner ℝ w Q := by
      have heq := heuler (chartFrame x w (α s))
      change regularizedEulerResidual F T α I E s (chartFrame x w (α s)) = 0 at heq
      unfold regularizedEulerResidual scalarCurvatureDifferential at heq
      dsimp only [Q, u, Function.comp_apply]
      rw [chartForceVector_inner, chartActionPotential_spatial_apply F hM04 T (hsrc hs) ht]
      linarith
    change HasDerivAt _
      ((F.metric (T - s ^ 2)).inner (α s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
            (curveVelocityWithin (n := n) α I) I E s) (chartFrame x w (α s)) +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s)
          (curveVelocityWithin (n := n) α I s) (chartFrame x w (α s)) +
        spatialFDeriv (chartActionMetric F T x) (s, u s) w (q s) (q s) / 2) s at hgraph
    rw [hQ] at hgraph
    exact hpair.unique (hgraph.congr_of_eventuallyEq hnear)
  have h := hPd.hasDerivAt
  rw [hderiv] at h
  exact h

end PoincareConjecture.M08
