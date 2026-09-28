import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.UniformLimit
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Proofs.M08.ChartCover
import Mathlib.Topology.Order.ProjIcc









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}



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



theorem exists_attainmentGauge (q : G.Point) :
    ∃ e : AttainmentGauge G, q ∈ e.source := by
  obtain ⟨j, U, lift, hU, hq, hlift, hright, hclock⟩ := M14.exists_smooth_gauge_lift G q
  exact ⟨⟨j, U, lift, (lift q).2, hU, hlift, hright, hclock⟩, hq⟩




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

end PoincareConjecture.Proofs.M46
