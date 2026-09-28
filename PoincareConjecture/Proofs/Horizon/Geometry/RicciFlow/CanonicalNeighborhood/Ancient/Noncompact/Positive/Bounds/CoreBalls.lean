import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.BoundaryBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive



theorem uniform_scalar_radius_volume_lower_of_services
    (P : NoncompactKappaServices.{u}) :
    ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧ C⁻¹ < kappa ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (K : AncientKappaSolution 3 M), ¬ IsCompact (univ : Set M) →
          ∀ (t : ℝ), t ≤ 0 → ∀ (p : M) (r : ℝ), 0 < r →
            scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
              ((K.flow.metric t).ball p r) = r⁻¹ ^ 2 →
            ENNReal.ofReal (kappa * r ^ 3) ≤
              calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball p r) := by
  obtain ⟨kappa, hkappa, hnoncollapse⟩ := P.universal_noncollapsing
  refine ⟨2 / kappa, kappa, div_pos (by norm_num) hkappa, hkappa, ?_, ?_⟩
  · have heq : (2 / kappa)⁻¹ = kappa / 2 := by simp
    rw [heq]
    linarith
  · intro M _ _ _ _ _ _ _ _ _ K hnoncompact t ht p r hr hscalar
    apply (hnoncollapse K (K.not_isRound_of_noncompact hnoncompact)) r hr t ht p r hr le_rfl
    intro s hs q hq
    rw [abs_of_nonneg (show 0 ≤ (K.flow.connection s).curvatureTensorNorm q from
      Real.sqrt_nonneg _)]
    apply (P.past_norm_le_scalar M K s t hs.2 ht q).trans
    apply le_trans ?_ hscalar.le
    exact le_csSup (K.scalar_range_ball_bddAbove ht p r) ⟨⟨q, hq⟩, rfl⟩



theorem uniform_scalar_radius_volume_lower
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧ C⁻¹ < kappa ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (K : AncientKappaSolution 3 M), ¬ IsCompact (univ : Set M) →
          ∀ (t : ℝ), t ≤ 0 → ∀ (p : M) (r : ℝ), 0 < r →
            scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
              ((K.flow.metric t).ball p r) = r⁻¹ ^ 2 →
            ENNReal.ofReal (kappa * r ^ 3) ≤
              calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball p r) := by
  exact uniform_scalar_radius_volume_lower_of_services P.noncompactServices



theorem exists_scalar_ball_enclosure_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [ConnectedSpace M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g),
        MetricComplete g → ∀ (N : EpsilonNeck g), N.epsilon ≤ epsilon₀ →
          ∀ (A : Set M), IsOpen A → frontier A = N.central_sphere →
            ∀ p ∈ A, ∀ r : ℝ, 0 < r →
              scalarCurvatureSupOn g D (g.ball p r) = r⁻¹ ^ 2 →
              closure (g.ball p r) ⊆ A ∪ N.carrier ∧
                IsCompact (closure (g.ball p r)) := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hbuffer⟩ :=
    EpsilonNeck.exists_scalar_radius_boundary_buffer.{u}
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D hc N hN A hA hfrontier p hp r hr hscalar
  refine ⟨?_, g.isCompact_closure_ball_of_metricComplete hc p r⟩
  classical
  by_cases hdisjoint : Disjoint (g.ball p r) (frontier A)
  · have hpball : p ∈ g.ball p r := by
      change g.edist p p < ENNReal.ofReal r
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
        ENNReal.ofReal_pos.mpr hr
    have hsubset := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      (g.isPreconnected_ball p r) hdisjoint ⟨p, hpball, hA.interior_eq.symm ▸ hp⟩
    apply (closure_mono (hsubset.trans interior_subset)).trans
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (N.central_sphere_subset (hfrontier ▸
        (show x ∈ frontier A from ⟨hx, fun hi => hxA (interior_subset hi)⟩)))
  · obtain ⟨x, hxball, hxfrontier⟩ := Set.not_disjoint_iff.mp hdisjoint
    have hbounded : BddAbove (range (fun y : g.ball p r => D.scalarCurvature y)) := by
      apply (((g.isCompact_closure_ball_of_metricComplete hc p r).image
        D.continuous_scalarCurvature).bddAbove).mono
      rintro _ ⟨y, rfl⟩
      exact ⟨y, subset_closure y.property, rfl⟩
    have hxscalar : D.scalarCurvature x ≤ r⁻¹ ^ 2 := by
      rw [← hscalar]
      exact le_csSup hbounded ⟨⟨x, hxball⟩, rfl⟩
    have hxneck := (hbuffer N D hN x (hfrontier ▸ hxfrontier) r hr hxscalar).2
    let : MetricSpace M := g.toMetricSpace
    have hxpr : dist x p < r := by
      simpa only [← g.toMetricSpace_ball, Metric.mem_ball] using hxball
    intro y hy
    have hypr : dist y p ≤ r := by
      apply Metric.closure_ball_subset_closedBall
      simpa only [← g.toMetricSpace_ball] using hy
    have hyx : y ∈ g.ball x (2 * r) := by
      rw [← g.toMetricSpace_ball, Metric.mem_ball]
      have htriangle := dist_triangle y p x
      rw [dist_comm p x] at htriangle
      linarith
    exact Or.inr (hxneck (subset_closure hyx))

end PoincareConjecture.NoncompactKappa.Positive
