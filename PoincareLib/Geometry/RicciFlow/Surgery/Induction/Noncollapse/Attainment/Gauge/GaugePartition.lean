import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Minimum.UniformLimit
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeLift
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.ChartCover
import Mathlib.Topology.Order.ProjIcc

/-!
# Compact buffers in actual inverse gauges

Proposition 16.4 and Claim 16.25, pp. 369 and 389-390. A finite partition
places the continuous limit and a common tail of its approximating paths
inside fixed compact subsets of actual smooth inverse neighborhoods.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M08
export PoincareMT.LGeometry (exists_compact_partition_of_uniform_limit)
end PoincareMT.M08

namespace PoincareMT.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- A local inverse of one supplied actual gauge, with its exact clock.
Source: Definition 3.38 and the direct method in Proposition 16.4. -/
structure AttainmentGauge (G : GeneralizedLGeometryTransport 3 X time I) where
  index : G.gaugeCover.index
  source : Set G.Point
  lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval index)).Point ×
    G.gaugeCover.spatial index
  center : G.gaugeCover.spatial index
  source_open : IsOpen source
  smooth : ContMDiffOn (spacetimeModel 3) (spacetimeModel 3) ∞ lift source
  right_inv : ∀ q ∈ source, (G.gaugeCover.cylinder index).toSpacetime (lift q) = q
  clock : ∀ q ∈ source, (lift q).1.val = G.spacetime.timeFunction q

variable {G : GeneralizedLGeometryTransport 3 X time I}

/-- The actual supplied gauges cover every point, including physical
boundary points. Source: Definition 3.38, p. 61. -/
theorem exists_attainmentGauge (q : G.Point) :
    ∃ e : AttainmentGauge G, q ∈ e.source := by
  obtain ⟨j, U, lift, hU, hq, hlift, hright, hclock⟩ := M14.exists_smooth_gauge_lift G q
  exact ⟨⟨j, U, lift, (lift q).2, hU, hlift, hright, hclock⟩, hq⟩

/-- Uniform convergence yields fixed compact buffers and one common
tail index in finitely many actual inverse gauges. Source: the direct
method in Proposition 16.4 and Claim 16.25, pp. 369, 389-390. -/
theorem exists_compact_gauge_partition {a b : ℝ} (hab : a ≤ b)
    (gamma : ℝ → G.Point) (hgamma : Continuous gamma) (paths : ℕ → ℝ → G.Point)
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn paths gamma atTop (Icc a b)) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (e : Fin m → AttainmentGauge G)
      (K : Fin m → Set G.Point) (N : ℕ),
      Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∀ i, IsCompact (K i) ∧
        gamma '' Icc (t i.castSucc) (t i.succ) ⊆ interior (K i) ∧ K i ⊆ (e i).source) ∧
      ∀ k ≥ N, ∀ i, MapsTo (paths k) (Icc (t i.castSucc) (t i.succ)) (K i) := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  let : MetricSpace G.Point := UniformSpace.metricSpace G.Point
  let : LocallyCompactSpace G.Point :=
    Manifold.locallyCompact_of_finiteDimensional (M := G.Point) (spacetimeModel 3)
  have hlim' : TendstoUniformlyOn paths gamma atTop (Icc a b) := by
    with_reducible_and_instances exact hlim
  exact M08.exists_compact_partition_of_uniform_limit
    (fun e : AttainmentGauge G => e.source) (fun e => e.source_open)
    exists_attainmentGauge hab gamma hgamma paths hlim'

/-- Clamping the actual continuous limit supplies the globally
continuous representative used by the finite-partition theorem.
Source: the direct method in Proposition 16.4, p. 369. -/
theorem clamp_uniform_limit {a b : ℝ} (hab : a ≤ b)
    (alpha : C(Icc a b, G.Point)) (paths : ℕ → ℝ → G.Point)
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformly (fun k (s : Icc a b) => paths k s.val) alpha atTop) :
    let gamma := fun s => alpha (projIcc a b hab s)
    Continuous gamma ∧
      (let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn paths gamma atTop (Icc a b)) := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  refine ⟨alpha.continuous.comp continuous_projIcc, ?_⟩
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hclamp : (fun s : Icc a b => alpha (projIcc a b hab s.val)) = alpha := by
    funext s
    rw [projIcc_of_mem _ s.property]
  simpa only [Function.comp_def, hclamp] using hlim

end PoincareMT.Proofs.M46
