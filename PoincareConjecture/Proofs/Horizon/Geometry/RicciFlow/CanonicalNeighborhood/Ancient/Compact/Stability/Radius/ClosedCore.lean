import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.BoundaryBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.BallBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [ConnectedSpace M]

theorem scalarCoreRadius_center_scalar_le (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hpos : ∀ x : M, 0 < D.scalarCurvature x) (p : M) :
    D.scalarCurvature p ≤ (scalarCoreRadius g D hc hpos p)⁻¹ ^ 2 := by
  let r := scalarCoreRadius g D hc hpos p
  have hr := scalarCoreRadius_spec g D hc hpos p
  have hbdd : BddAbove (range (fun x : g.ball p r => D.scalarCurvature x)) := by
    apply (((g.isCompact_closure_ball_of_metricComplete hc p r).image
      D.continuous_scalarCurvature).bddAbove).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, subset_closure x.property, rfl⟩
  have hp : p ∈ g.ball p r := by
    change g.edist p p < ENNReal.ofReal r
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hr.1
  rw [← hr.2]
  exact le_csSup hbdd ⟨⟨p, hp⟩, rfl⟩

theorem CapCertificate.exists_closedCore_ball_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [ConnectedSpace M] {g : RiemannianMetric 3 M},
        ∀ (A : CapCertificate g) (hc : MetricComplete g)
          (hpos : ∀ x : M, 0 < A.connection.scalarCurvature x),
          A.epsilon ≤ epsilon₀ → ∀ x ∈ A.closed_core,
            closure (g.ball x (scalarCoreRadius g A.connection hc hpos x)) ⊆ A.carrier := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hbuffer⟩ :=
    EpsilonNeck.exists_scalar_radius_boundary_buffer.{u}
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ g A hc hpos hepsilon x hx
  by_cases hxcore : x ∈ A.core
  · have heq := eq_scalarCoreRadius_of_spec g A.connection hc hpos x
      (A.core_radius_pos x hxcore) (A.core_radius_eq x hxcore)
    rw [← heq]
    exact A.core_ball_subset x hxcore
  · have hxboundary : x ∈ A.boundary_sphere := by
      rw [← A.core_frontier_eq_boundary, frontier,
        A.closed_core_compact.isClosed.closure_eq]
      exact ⟨hx, fun hi => hxcore (A.core_eq_interior_closed_core.symm ▸ hi)⟩
    have hneck : A.boundary_neck.epsilon ≤ epsilon₀ :=
      A.boundary_neck_epsilon ▸ hepsilon
    have hr := scalarCoreRadius_spec g A.connection hc hpos x
    have hcontain := (hbuffer A.boundary_neck A.connection hneck x
      (A.boundary_eq_neck_sphere ▸ hxboundary) _ hr.1
      (scalarCoreRadius_center_scalar_le g A.connection hc hpos x)).2
    apply (closure_mono ?_).trans (hcontain.trans A.boundary_neck_subset)
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith [hr.1]))

theorem CapCertificate.exists_uniform_closedCore_ball_buffer_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [ConnectedSpace M] {g : RiemannianMetric 3 M},
        ∀ (A : CapCertificate g) (hc : MetricComplete g)
          (hpos : ∀ x : M, 0 < A.connection.scalarCurvature x),
          A.epsilon ≤ epsilon₀ → ∃ delta : ℝ, 0 < delta ∧ ∀ x ∈ A.closed_core,
            closure (g.ball x ((1 + delta) * scalarCoreRadius g A.connection hc hpos x)) ⊆
              A.carrier := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hinside⟩ :=
    CapCertificate.exists_closedCore_ball_threshold.{u}
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ g A hc hpos hepsilon
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hc
  let rho := scalarCoreRadius g A.connection hc hpos
  have hclosure (x : M) (r : ℝ) (hr : 0 < r) :
      closure (g.ball x r) = Metric.closedBall x r := by
    rw [← g.toMetricSpace_ball]
    exact CompactKappaCoreRadius.closure_ball_eq_of_approximate_split
      (fun x y _ _ hr hε => g.approximate_split_toMetricSpace x y hr hε) x hr
  have hball (x : M) (hx : x ∈ A.closed_core) :
      Metric.closedBall x (rho x) ⊆ A.carrier := by
    rw [← hclosure x (rho x) (scalarCoreRadius_spec g A.connection hc hpos x).1]
    exact hinside A hc hpos hepsilon x hx
  obtain ⟨delta, hdelta, hbuffer⟩ :=
    CompactKappaCoreRadius.exists_multiplicative_closedBall_buffer
      A.closed_core_compact A.carrier_open
      (continuous_scalarCoreRadius g A.connection hc hpos).continuousOn hball
  refine ⟨delta, hdelta, fun x hx => ?_⟩
  rw [hclosure x _ (mul_pos (by linarith) (scalarCoreRadius_spec g A.connection hc hpos x).1)]
  exact hbuffer x hx

end PoincareConjecture
