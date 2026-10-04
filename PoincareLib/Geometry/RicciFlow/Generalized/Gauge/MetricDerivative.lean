import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.MetricDerivative.Time
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.MetricDerivative.ProductRule
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.SectionTransport
import PoincareLib.Geometry.Spacetime.Horizontal.Connection

/-!
# Metric differentiation under a moving gauge

The horizontal metric defect and the transported connection identify the
derivative of the actual pullback metric. The two derivatives of the pulled
back sections cancel, leaving the negative spatial metric Lie derivative.

The product-rule argument follows the inspected AxelWorkspace theorem
`MorganTianLib.hasDerivWithinAt_gaugePullbackValue_of_jointSmooth`, revision
`f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e`. Here local section transport replaces
global diffeomorphisms, and normalized interval tangents treat endpoints.

Source: Morgan--Tian, Definition 1.4, pp. 5--7, and Definitions 3.34--3.38,
Remark 3.37, pp. 59--61.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open scoped Manifold ContDiff Bundle Topology
open Set Filter Bundle

universe u v

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ s : ℝ, SpacetimeSliceGeometry F s}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

private theorem movingGaugeTimeVelocity_time
    (e : MovingSpacetimeGauge F T C) (t : T.Point) (x : C) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction
      (e.toSpacetime (t, x)) (movingGaugeTimeVelocity e t x)) = 1 := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  have hd := movingGauge_hasDerivWithinAt_comp e (f := F.timeFunction) t x
    (F.time_smooth.mdifferentiableAt (by simp))
  have heq (s : ℝ) (hs : s ∈ K.domain) :
      s = F.timeFunction (e.toSpacetime (T.realParam s, x)) := by
    rw [e.time_eq, T.realParam_val hs]
  have h := hd.congr heq (heq t.val t.property)
  exact (uniqueDiffWithinAt_of_spacetimeInterval K t).eq_deriv K.domain h
    (hasDerivWithinAt_id t.val K.domain)

private theorem movingGauge_metric_derivative_on_sections
    (D : LeafwiseLeviCivitaFamily F S) (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (V W : HorizontalSection F) (O : Set F.Point) (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O)
    (hW : IsSmoothHorizontalSectionOn F W O)
    (t : T.Point) (x : C) (hp : e.toSpacetime (t, x) ∈ O) :
    HasDerivWithinAt
      (fun s => (G.metric s).inner x
        (pullbackHorizontalSection G V t x) (pullbackHorizontalSection G W t x))
      (horizontalMetricLieDerivative F (e.toSpacetime (t, x))
        (V (e.toSpacetime (t, x))) (W (e.toSpacetime (t, x))) -
        ordinaryMetricLieDerivative (G.metric t.val) (c t.val) (movingGaugeDrift G t) x
          (pullbackHorizontalSection G V t x) (pullbackHorizontalSection G W t x))
      K.domain t.val := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  have hVd := (hV.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp)
  have hWd := (hW.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp)
  have hpair := (F.horizontalMetric.contMDiff _).mdifferentiableAt (by simp)
    |>.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : F.Point => ℝ) hVd hWd
  rw [mdifferentiableAt_totalSpace] at hpair
  have hpair' : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ)
      (fun q => F.horizontalMetric.inner q (V q) (W q)) (e.toSpacetime (t, x)) := hpair.2
  have hpder := movingGauge_hasDerivWithinAt_comp e t x hpair'
  have hunique := uniqueDiffWithinAt_of_spacetimeInterval K t
  have ha := movingGauge_hasDerivWithinAt_pullbackSection e G V O hO hV t x hp
  have hb := movingGauge_hasDerivWithinAt_pullbackSection e G W O hO hW t x hp
  have hprod := movingMetric_hasDerivWithinAt_pair G.smooth t.property hunique x ha hb
  have heq (s : ℝ) (hs : s ∈ K.domain) :
      (G.metric s).inner x (pullbackHorizontalSection G V (T.realParam s) x)
        (pullbackHorizontalSection G W (T.realParam s) x) =
      F.horizontalMetric.inner (e.toSpacetime (T.realParam s, x))
        (V (e.toSpacetime (T.realParam s, x)))
        (W (e.toSpacetime (T.realParam s, x))) := by
    have hm := G.metric_eq (T.realParam s) x
      (pullbackHorizontalSection G V (T.realParam s) x)
      (pullbackHorizontalSection G W (T.realParam s) x)
    rw [T.realParam_val hs] at hm
    simpa only [pullbackHorizontalSection, ContinuousLinearEquiv.apply_symm_apply] using hm
  have hpder' := hpder.congr heq (heq t.val t.property)
  have heval := hunique.eq_deriv K.domain hpder' hprod
  simp only [T.realParam_coe] at heval
  have hdefect := rawHorizontalCovariantDerivative_metric_defect D hVd hWd
    (movingGaugeTimeVelocity e t x)
  rw [movingGaugeTimeVelocity_time e t x, one_mul] at hdefect
  have htransport := movingGaugeSectionTransportFields D e G c
  have hconnV := htransport.horizontal_derivative_eq V O hO hV t x hp 1 0
  have hconnW := htransport.horizontal_derivative_eq W O hO hW t x hp 1 0
  simp only [one_smul, map_zero, add_zero] at hconnV hconnW
  change rawHorizontalCovariantDerivative D V (e.toSpacetime (t, x))
    (movingGaugeTimeVelocity e t x) = _ at hconnV
  change rawHorizontalCovariantDerivative D W (e.toSpacetime (t, x))
    (movingGaugeTimeVelocity e t x) = _ at hconnW
  rw [hconnV, hconnW] at hdefect
  have hVval : V (e.toSpacetime (t, x)) =
      G.spatialTangentEquiv t x (pullbackHorizontalSection G V t x) := by
    simp only [pullbackHorizontalSection, ContinuousLinearEquiv.apply_symm_apply]
  have hWval : W (e.toSpacetime (t, x)) =
      G.spatialTangentEquiv t x (pullbackHorizontalSection G W t x) := by
    simp only [pullbackHorizontalSection, ContinuousLinearEquiv.apply_symm_apply]
  rw [hWval, ← G.metric_eq, hVval, ← G.metric_eq] at hdefect
  rw [← hVval, ← hWval] at hdefect
  simp only [map_sub, sub_apply] at hdefect
  have hs := G.smooth.contDiffWithinAt_inner_time t.property x
    (pullbackHorizontalSection G V t x) (pullbackHorizontalSection G W t x)
  have hd := (hs.differentiableWithinAt (by simp)).hasDerivWithinAt
  apply hd.congr_deriv
  unfold ordinaryMetricLieDerivative
  linarith

/-- The exact metric-derivative field of `MovingGaugeCalculus`, for arbitrary
carrier universes, all spatial dimensions, and every included interval point. -/
theorem movingGauge_metric_derivative
    (D : LeafwiseLeviCivitaFamily F S) (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (G.metric s).inner x u v)
      (horizontalMetricLieDerivative F (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v) -
          ordinaryMetricLieDerivative (G.metric t.val) (c t.val)
            (movingGaugeDrift G t) x u v) K.domain t.val := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  let V := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (G.spatialTangentEquiv t x u)
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (G.spatialTangentEquiv t x v)
  obtain ⟨U, hU, hV⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞)
    (spacetimeModel n) (EuclideanSpace ℝ (Fin n)) (G.spatialTangentEquiv t x u)
  obtain ⟨U', hU', hW⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞)
    (spacetimeModel n) (EuclideanSpace ℝ (Fin n)) (G.spatialTangentEquiv t x v)
  obtain ⟨O, hOsub, hO, hp⟩ := mem_nhds_iff.mp (inter_mem hU hU')
  have hd := movingGauge_metric_derivative_on_sections D G c V W O hO
    (hV.mono fun _ h => (hOsub h).1) (hW.mono fun _ h => (hOsub h).2) t x hp
  simpa only [V, W, pullbackHorizontalSection, FiberBundle.extend_apply_self,
    ContinuousLinearEquiv.symm_apply_apply] using hd

end PoincareMT
