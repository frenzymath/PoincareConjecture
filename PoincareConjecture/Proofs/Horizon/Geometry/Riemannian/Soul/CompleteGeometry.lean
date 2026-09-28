import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.ExhaustionFunction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.BusemannConcavity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [MetricSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_smooth_metric_segment_of_complete
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal) (p q : M) :
    ∃ curve : ℝ → M, curve 0 = p ∧ curve (dist p q) = q ∧
      IsMinimizingOn curve (Icc 0 (dist p q)) ∧
      g.IsGeodesicOn curve (Icc 0 (dist p q)) := by
  by_cases hpq : p = q
  · subst q
    refine ⟨fun _ => p, rfl, rfl, ?_, g.isGeodesicOn_const p _⟩
    intro s hs t ht
    simp only [dist_self, mem_Icc] at hs ht ⊢
    have hs0 : s = 0 := by linarith [hs.1, hs.2]
    have ht0 : t = 0 := by linarith [ht.1, ht.2]
    simp [hs0, ht0]
  · have hd : 0 < dist p q := dist_pos.mpr hpq
    obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
      g.exists_minimizing_geodesic_of_metricComplete hcomplete p q
    let curve : ℝ → M := fun t => γ ((dist p q)⁻¹ * t)
    have hparam {t : ℝ} (ht : t ∈ Icc 0 (dist p q)) :
        (dist p q)⁻¹ * t ∈ Icc (0 : ℝ) 1 := by
      rw [← div_eq_inv_mul]
      exact ⟨div_nonneg ht.1 hd.le, (div_le_one hd).mpr ht.2⟩
    refine ⟨curve, by simp [curve, hγ0], by simp [curve, hd.ne', hγ1], ?_, ?_⟩
    · intro s hs t ht
      change dist (γ ((dist p q)⁻¹ * s)) (γ ((dist p q)⁻¹ * t)) = _
      rw [hdist, hmin _ (hparam hs) _ (hparam ht), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg _), ← hdist p q]
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hd)]
      field_simp
    · intro t ht
      apply hγ.comp_mul (dist p q)⁻¹ t
      have h := hparam ht
      exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem hasMinimizingSegments_of_complete
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal) :
    HasMinimizingSegments M := by
  intro p q
  obtain ⟨curve, h0, h1, hmin, _⟩ :=
    g.exists_smooth_metric_segment_of_complete hcomplete hdist p q
  exact ⟨curve, h0, h1, hmin⟩

theorem properSpace_of_complete
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal) : ProperSpace M := by
  apply ProperSpace.of_isCompact_closedBall_of_le 0
  intro x r hr
  have hset : closedBall x r = {y | g.edist x y ≤ ENNReal.ofReal r} := by
    ext y
    rw [mem_closedBall, dist_comm, hdist]
    exact (ENNReal.le_ofReal_iff_toReal_le (g.edist_ne_top x y) hr).symm
  rw [hset]
  exact g.isCompact_closedBall_of_metricComplete hcomplete x r

theorem isCompact_horoballIntersection_of_nonnegativeSectional
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (p : M) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (horoballIntersection p r) := by
  let : ProperSpace M := g.properSpace_of_complete hcomplete hdist
  apply isCompact_horoballIntersection p hr
  intro q hq
  obtain ⟨curve, h0, h1, hmin, hgeo⟩ :=
    g.exists_smooth_metric_segment_of_complete hcomplete hdist p q
  refine ⟨curve, h0, h1, hmin, ?_⟩
  apply mapsTo_horoballIntersection_of_concaveOn
    (fun ray hray _ => g.concaveOn_busemann_of_nonnegativeSectional
      D hcomplete hsec hdist hray hgeo)
  · rw [h0]
    exact closedBall_subset_horoballIntersection p r (by simpa only [mem_closedBall, dist_self] using hr)
  · simpa only [h1] using hq

end PoincareConjecture.RiemannianMetric
