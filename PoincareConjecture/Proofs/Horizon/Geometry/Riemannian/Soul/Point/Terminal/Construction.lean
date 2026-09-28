import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.MaximalDepth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CompleteGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [MetricSpace M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_maximal_innerParallelSet_of_nonnegativeSectional
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (p : M) {c : ℝ} (hc : 0 < c) :
    let K := horoballIntersection p c
    ∃ R : ℝ, 0 < R ∧
      let S := {x ∈ K | R ≤ infDist x Kᶜ}
      S.Nonempty ∧ IsCompact S ∧
      (∀ x ∈ K, infDist x Kᶜ ≤ R) ∧
      (∀ s : ℝ, R < s → {x ∈ K | s ≤ infDist x Kᶜ} = ∅) ∧
      interior S = ∅ ∧ S = horoballIntersection p (c - R) ∧
      ∀ (curve : ℝ → M) (a b : ℝ), g.IsGeodesicOn curve (Icc a b) →
        curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S := by
  let : ProperSpace M := g.properSpace_of_complete hcomplete hdist
  let K := horoballIntersection p c
  have hK : IsCompact K :=
    g.isCompact_horoballIntersection_of_nonnegativeSectional D hcomplete hsec hdist p hc.le
  have hp : p ∈ K := closedBall_subset_horoballIntersection p c (by
    simpa only [mem_closedBall, dist_self] using hc.le)
  have hcompl : Kᶜ.Nonempty := nonempty_compl.mpr hK.ne_univ
  have hdepth : 0 < infDist p Kᶜ := by
    apply hc.trans_le
    apply (le_infDist hcompl).2
    intro y hy
    by_contra h
    apply hy
    apply closedBall_subset_horoballIntersection p c
    simpa only [mem_closedBall, dist_comm] using (not_le.mp h).le
  obtain ⟨R, hR, hne, hcompact, hmax, hempty⟩ :=
    exists_maximal_innerParallelSet hK hp hdepth
  have hsegments := g.hasMinimizingSegments_of_complete hcomplete hdist
  have hshift : {x ∈ K | R ≤ infDist x Kᶜ} = horoballIntersection p (c - R) :=
    innerParallelSet_eq_shift hsegments p c hcompl hR.le
  refine ⟨R, hR, hne, hcompact, hmax, hempty,
    interior_maximal_innerParallelSet_eq_empty hsegments hcompl hR hmax, hshift, ?_⟩
  intro curve a b hgeo ha hb
  rw [hshift] at ha hb ⊢
  exact mapsTo_horoballIntersection_of_concaveOn
    (fun ray hray _ => g.concaveOn_busemann_of_nonnegativeSectional
      D hcomplete hsec hdist hray hgeo) ha hb

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

theorem exists_compact_totallyConvex_set_empty_interior
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ interior S = ∅ ∧
      ∀ (curve : ℝ → M) (a b : ℝ), g.IsGeodesicOn curve (Icc a b) →
        curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace g.edist_ne_top
  obtain ⟨R, _, hne, hc, _, _, hi, _, hconv⟩ :=
    g.exists_maximal_innerParallelSet_of_nonnegativeSectional D hcomplete hsec
      (fun _ _ => rfl) p (c := 1) zero_lt_one
  exact ⟨{x ∈ horoballIntersection p 1 |
    R ≤ infDist x (horoballIntersection p 1)ᶜ}, hne, hc, hi, hconv⟩

end PoincareConjecture.RiemannianMetric
