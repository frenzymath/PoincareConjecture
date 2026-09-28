import PoincareConjecture.Proofs.M14.Sec6_4_GaugeFirstDerivatives










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
  (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
  (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
    (horizontalScalarCurvature G.leafwise))
  (hM04 : RicciFlowCurvatureTheory.{0}) (T : ℝ) {C : Set ℝ}
  (hC : UniqueDiffOn ℝ C)
  (htime : ∀ s ∈ C, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
  (x y : G.gaugeCover.spatial b) {s : ℝ} (hs : s ∈ C) (hsN : C ∈ 𝓝 s)
  (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
  (ht : T - s ^ 2 = t.val)

include hCoordinates hscalar hM04 hC htime hs hsN ht




theorem gauge_surfaceIndex_expression (a v d : EuclideanSpace ℝ (Fin n)) :
    let m := M08.chartActionMetric W.flow T x
    let Γ := M08.closedChartConnection W.flow T x C
    let P₀ := fun z => M08.chartActionPotential W.flow T x (s, z)
    let q := (G.gaugeCover.cylinder b).toSpacetime (t, y)
    let j := (G.gaugeCover.metric b).spatialTangentEquiv t y
    m (s, y.val) d d +
        m (s, y.val) (M08.coordinateCurvature Γ (s, y.val) v a v) a -
        m (s, y.val) (fderiv ℝ Γ (s, y.val) (1, 0) v v) a +
        (fderiv ℝ (fderiv ℝ P₀) y.val v v - fderiv ℝ P₀ y.val (Γ (s, y.val) v v)) =
      G.spacetime.horizontalMetric.inner q (j d) (j d) +
        horizontalRiemann G.leafwise q (j v) (j a) (j a) (j v) +
        2 * s ^ 2 * M14HorizontalHessianPairing G q (j v) (j v) -
        4 * s * M14HorizontalRicciDerivativePairing G q (j v) (j a) (j v) +
        2 * s * M14HorizontalRicciDerivativePairing G q (j a) (j v) (j v) := by
  dsimp only
  rw [gauge_coordinateCurvature_pair b W hCoordinates hM04 T hC htime x y hs hsN t ht,
    gauge_chartConnection_time_pair b W hCoordinates hM04 T hC htime x y hs hsN t ht,
    gauge_chartActionPotential_hessian b W hCoordinates hscalar hM04 T hC htime x y hs t ht,
    gauge_chartActionMetric b W T x y s t ht]
  have hsym := horizontalRicciDerivativePairing_symm
    ((G.gaugeCover.cylinder b).toSpacetime (t, y))
    ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
    ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
    ((G.gaugeCover.metric b).spatialTangentEquiv t y a)
  simp only [M14BcalPairing, hsym]
  ring




theorem gauge_surfaceEuler_expression (a d z : EuclideanSpace ℝ (Fin n)) :
    let m := M08.chartActionMetric W.flow T x
    let P₀ := fun v => M08.chartActionPotential W.flow T x (s, v)
    let q := (G.gaugeCover.cylinder b).toSpacetime (t, y)
    let j := (G.gaugeCover.metric b).spatialTangentEquiv t y
    m (s, y.val) d z - fderiv ℝ P₀ y.val z +
        fderiv ℝ m (s, y.val) (1, 0) a z =
      G.spacetime.horizontalMetric.inner q (j d) (j z) -
        2 * s ^ 2 * M14HorizontalScalarDifferential G q (j z).val +
        4 * s * horizontalRicci G.leafwise q (j a) (j z) := by
  dsimp only
  rw [gauge_chartActionPotential_differential b W hCoordinates hscalar hM04 T htime x y hs t ht,
    gauge_chartActionMetric_time_pair b W hCoordinates hM04 T hC htime x y hs hsN t ht,
    gauge_chartActionMetric b W T x y s t ht]

end PoincareConjecture.M14
