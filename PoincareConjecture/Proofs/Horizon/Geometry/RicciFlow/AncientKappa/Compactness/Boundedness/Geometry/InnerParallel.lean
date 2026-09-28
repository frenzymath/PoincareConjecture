import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CompleteGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem le_frontier_dist_iff_le_compl_dist
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {C : Set M} (hC : IsClosed C) {x : M} (hx : x ∈ C) {r : ℝ} :
    (∀ y ∈ frontier C, r ≤ (g.edist x y).toReal) ↔
      (∀ y ∉ C, r ≤ (g.edist x y).toReal) := by
  constructor
  · intro hfront
    by_cases hr : r ≤ 0
    · exact fun y _ => hr.trans ENNReal.toReal_nonneg
    have hxint : x ∈ interior C := by
      by_contra hnot
      have h := hfront x ⟨hC.closure_eq.symm ▸ hx, hnot⟩
      have hself : g.edist x x = 0 := by
        let : MetricSpace M := g.toMetricSpace
        exact edist_self x
      rw [hself, ENNReal.toReal_zero] at h
      exact hr h
    exact fun y hy => g.frontier_distance_le_of_not_mem_interior hc hxint hfront
      (fun hyint => hy (interior_subset hyint))
  · intro hcompl y hy
    have hclosed : IsClosed {z | r ≤ (g.edist x z).toReal} :=
      isClosed_le continuous_const (g.continuous_toReal_edist x)
    have hsub : Cᶜ ⊆ {z | r ≤ (g.edist x z).toReal} := hcompl
    have hycompl : y ∈ closure Cᶜ := by
      rw [closure_compl]
      exact hy.2
    exact (closure_minimal hsub hclosed) hycompl

theorem exists_compact_convex_exhaustion_with_innerParallel
    [NoncompactSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    ∃ C : ℝ → Set M,
      (∀ r : ℝ, 0 ≤ r → IsCompact (C r)) ∧
      (∀ r : ℝ, 0 ≤ r → p ∈ C r) ∧
      Monotone C ∧ (⋃ r : ℝ, C r) = univ ∧
      (∀ r s : ℝ, r < s → C r ⊆ interior (C s)) ∧
      (∀ r : ℝ, ∀ (curve : ℝ → M) (a b : ℝ),
        g.IsGeodesicOn curve (Icc a b) → curve a ∈ C r → curve b ∈ C r →
          MapsTo curve (Icc a b) (C r)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        C s = {x ∈ C t | ∀ y ∈ frontier (C t), t - s ≤ (g.edist x y).toReal} := by
  let : MetricSpace M := g.toMetricSpace
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  let : ProperSpace M := g.properSpace_of_complete hc hdist
  have hsegments := g.hasMinimizingSegments_of_complete hc hdist
  let C : ℝ → Set M := horoballIntersection p
  have hcompact (r : ℝ) (hr : 0 ≤ r) : IsCompact (C r) :=
    g.isCompact_horoballIntersection_of_nonnegativeSectional D hc hsec hdist p hr
  refine ⟨C, hcompact, ?_, horoballIntersection_mono p,
    iUnion_horoballIntersection p, ?_, ?_, ?_⟩
  · intro r hr
    exact closedBall_subset_horoballIntersection p r (by
      simpa only [mem_closedBall, dist_self] using hr)
  · intro r s hrs
    exact horoballIntersection_subset_interior p hrs
  · intro r curve a b hcurve ha hb
    exact mapsTo_horoballIntersection_of_concaveOn
      (fun ray hray _ => g.concaveOn_busemann_of_nonnegativeSectional
        D hc hsec hdist hray hcurve) ha hb
  · intro s t hs hst
    have ht : 0 ≤ t := hs.trans hst
    have hne : (C t)ᶜ.Nonempty := nonempty_compl.mpr (hcompact t ht).ne_univ
    have hparallel := innerParallelSet_eq_shift hsegments p t hne (sub_nonneg.mpr hst)
    have hshift : t - (t - s) = s := by ring
    rw [hshift] at hparallel
    change {x ∈ C t | t - s ≤ infDist x (C t)ᶜ} = C s at hparallel
    rw [← hparallel]
    ext x
    constructor
    · rintro ⟨hx, hd⟩
      refine ⟨hx, (g.le_frontier_dist_iff_le_compl_dist hc
        (isClosed_horoballIntersection p t) hx).2 ?_⟩
      intro y hy
      rw [← hdist]
      exact hd.trans (infDist_le_dist_of_mem hy)
    · rintro ⟨hx, hd⟩
      refine ⟨hx, (le_infDist hne).2 ?_⟩
      intro y hy
      rw [hdist]
      exact (g.le_frontier_dist_iff_le_compl_dist hc
        (isClosed_horoballIntersection p t) hx).1 hd y hy

end PoincareConjecture.RiemannianMetric
