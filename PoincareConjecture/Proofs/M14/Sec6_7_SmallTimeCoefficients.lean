import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeGaugeAction
import PoincareConjecture.Proofs.M14.Mathlib.QuadraticCoefficientBounds
import PoincareConjecture.Proofs.M14.Mathlib.CompactCoordinateBox
import PoincareConjecture.Definitions.M14Exponential

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

open Set
open scoped Manifold ContDiff Bundle NNReal Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space {p : G.Point} : T2Space (G.Horizontal p) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal p

attribute [local instance] horizontal_t2Space

theorem exponential_gauge_clock_smooth
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x)
    (b : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (htime : ∀ q ∈ U, (lift q).1.val = G.spacetime.timeFunction q)
    {D : Set ℝ} (hsurv : ∀ s ∈ D, (Z, s) ∈ E.domain)
    (hsrc : ∀ s ∈ D, E.gamma Z s ∈ U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ (fun s => (lift (E.gamma Z s)).1) D ∧
      ∀ s ∈ D, (lift (E.gamma Z s)).1.val = T - s ^ 2 := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨metric⟩
  have hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (E.gamma Z) D :=
    E.family_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn hsurv
  refine ⟨fun s hs => ((hlift.comp hγ hsrc) s hs).fst, ?_⟩
  intro s hs
  exact (htime _ (hsrc s hs)).trans (E.clock Z s (hsurv s hs))

theorem squareGauge_compact_coefficient_bounds
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index) (x₀ : G.gaugeCover.spatial b)
    {d : ℝ} (hd : 0 < d)
    (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (hθ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ θ (Icc 0 d))
    (hclock : ∀ s ∈ Icc 0 d, (θ s).val = T - s ^ 2)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    (hconvex : Convex ℝ S) (hsub : S ⊆ G.gaugeCover.spatial b) :
    let B := squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
    let V := squarePotentialCoefficient b θ x₀
    ∃ m : ℝ, 0 < m ∧ ∃ K : ℝ≥0,
      (∀ z ∈ Icc 0 d ×ˢ S, ∀ v : EuclideanSpace ℝ (Fin n), m * ‖v‖ ^ 2 ≤ B z v v) ∧
      ∀ s ∈ Icc 0 d,
        LipschitzOnWith K (fun z => B (s, z)) S ∧
        LipschitzOnWith K
          (fun z => M08.spatialWithinFDeriv (Icc 0 d) (G.gaugeCover.spatial b) B (s, z)) S ∧
        LipschitzOnWith K
          (fun z => M08.spatialWithinFDeriv (Icc 0 d) (G.gaugeCover.spatial b) V (s, z)) S := by
  dsimp only
  apply exists_quadratic_coefficient_bounds hd (G.gaugeCover.spatial b).isOpen hS hconvex hsub
  · exact squareMetricCoefficient_contDiffOn (G.gaugeCover.spatial b)
      (G.gaugeCover.metric b).metric (G.gaugeCover.metric b).smooth T x₀ (fun s hs => by
        rw [← hclock s hs]
        exact (θ s).property)
  · exact squarePotentialCoefficient_contDiffOn b θ x₀ hM12 hθ
  · intro z hz v hv
    exact squareMetricCoefficient_pos (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric
      T x₀ z.1 hz.2 v hv

end PoincareConjecture.M14
