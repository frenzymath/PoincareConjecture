import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MetricPairBase







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance variationMetricPairDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance variationMetricPairDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance variationMetricPairBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance variationMetricPairBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem chartFrame_curveVelocity {α : ℝ → M} {x : M} {s : ℝ}
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (α s) =
      curveVelocity (n := n) α s := by
  unfold chartFrame
  rw [chart_deriv_eq_velocity hx hα]
  exact Bundle.Trivialization.symmL_continuousLinearMapAt
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) hx _

set_option maxHeartbeats 1000000 in
theorem parametricExtension_metric_pair_moving_graph {J I : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (hI : IsOpen I) {α : ℝ → M}
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I))
    {x : M} {s : ℝ} (hs : s ∈ I)
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (ht : T - s ^ 2 ∈ interior J)
    {w : ℝ → EuclideanSpace ℝ (Fin n)} {k : EuclideanSpace ℝ (Fin n)}
    (hw : HasDerivAt w k s) :
    HasDerivAt (fun r ↦ (F.metric (T - r ^ 2)).inner (α r)
        (E.extension r (α r)) (chartFrame x (w r) (α r)))
      ((F.metric (T - s ^ 2)).inner (α s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
            (curveVelocityWithin (n := n) α I) I E s) (chartFrame x (w s) (α s)) +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s)
          (curveVelocityWithin (n := n) α I s) (chartFrame x (w s) (α s)) +
        spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (α s))
          (w s) (deriv ((extChartAt (𝓡 n) x) ∘ α) s)
            (deriv ((extChartAt (𝓡 n) x) ∘ α) s) / 2 +
        chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s))
          (deriv ((extChartAt (𝓡 n) x) ∘ α) s) k) s := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let c := fun r ↦ e.continuousLinearMapAt ℝ (α r) (E.extension r (α r))
  let G := fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r))
  let P := fun r ↦ G r (c r)
  have hud : DifferentiableAt ℝ ((extChartAt (𝓡 n) x) ∘ α) s :=
    ((((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hx).mdifferentiableAt
      (by simp)).comp s hα)).differentiableAt
  have hdom : (s, extChartAt (𝓡 n) x (α s)) ∈ chartActionDomain F T x := by
    refine ⟨squareTime_mem_interior_preimage ht, (extChartAt (𝓡 n) x).map_source ?_⟩
    simpa only [extChartAt_source] using hx
  have hGbase := (((chartActionMetric_contDiffOn F T x) _ hdom).contDiffAt
    ((chartActionDomain_open F T x).mem_nhds hdom)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G s :=
    hGbase.comp (f := fun r : ℝ ↦ (r, extChartAt (𝓡 n) x (α r))) s
      (differentiableAt_id.prodMk hud)
  have hc : DifferentiableAt ℝ c s := by
    have hcoord := (parametricExtension_chart_contMDiffAt E hx
      (E.graph_mem s hs)).mdifferentiableAt (by simp)
    exact (hcoord.comp (f := fun r : ℝ ↦ (r, α r)) s
      (mdifferentiableAt_id.prodMk hα)).differentiableAt
  have hP : DifferentiableAt ℝ P s := hG.clm_apply hc
  have hnear : ∀ᶠ r in 𝓝 s, α r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source :=
    hα.continuousAt.preimage_mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hx)
  have hpair (r : ℝ) (hr : α r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
      (z : EuclideanSpace ℝ (Fin n)) : P r z =
      (F.metric (T - r ^ 2)).inner (α r) (E.extension r (α r)) (chartFrame x z (α r)) := by
    dsimp only [P, G]
    rw [chartActionMetric_apply F T hr]
    exact congrArg (fun v : TangentSpace (𝓡 n) (α r) ↦
      (F.metric (T - r ^ 2)).inner (α r) v (chartFrame x z (α r)))
        (e.symmL_continuousLinearMapAt hr _)
  have hfixed := parametricExtension_metric_pair_graph F T hI E hs hx hα ht (w s)
  have hfixedP := hfixed.congr_of_eventuallyEq
    (show (fun r ↦ P r (w s)) =ᶠ[𝓝 s] _ from hnear.mono (fun r hr ↦ hpair r hr (w s)))
  have h := linear_moving_vector_hasDerivAt hP hw hfixedP
  have hcs : c s = deriv ((extChartAt (𝓡 n) x) ∘ α) s := by
    dsimp only [c]
    rw [E.agrees s hs]
    simp only [curveVelocityWithin, mfderivWithin_of_mem_nhds (hI.mem_nhds hs)]
    exact (chart_deriv_eq_velocity hx hα).symm
  have hPk : P s k = chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s))
      (deriv ((extChartAt (𝓡 n) x) ∘ α) s) k := by
    dsimp only [P, G]
    rw [hcs]
  rw [hPk] at h
  exact h.congr_of_eventuallyEq
    (hnear.mono (fun r hr ↦ (hpair r hr (w r)).symm))

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
