import PoincareConjecture.Statements.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem AncientKappaSolution.scalar_range_ball_bddAbove
    (K : AncientKappaSolution 3 M) {t : ℝ} (ht : t ≤ 0) (p : M) (r : ℝ) :
    BddAbove (range (fun x : (K.flow.metric t).ball p r =>
      (K.flow.connection t).scalarCurvature x)) := by
  have hcompact := (K.flow.metric t).isCompact_closure_ball_of_metricComplete
    (K.complete t ht) p r
  apply (hcompact.image (K.flow.connection t).continuous_scalarCurvature).bddAbove.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨x, subset_closure x.property, rfl⟩

theorem scalar_radius_volume_lower
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) {kappa t r : ℝ}
    (hnoncollapse : AncientKappaNoncollapsed K.flow kappa)
    (ht : t ≤ 0) (p : M) (hr : 0 < r)
    (hscalar : scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
      ((K.flow.metric t).ball p r) ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball p r) := by
  apply hnoncollapse r hr t ht p r hr le_rfl
  intro s hs q hq
  rw [abs_of_nonneg (show 0 ≤ (K.flow.connection s).curvatureTensorNorm q from
    Real.sqrt_nonneg _)]
  apply (P.past_norm_le_scalar M K s t hs.2 ht q).trans
  apply le_trans ?_ hscalar
  exact le_csSup (K.scalar_range_ball_bddAbove ht p r) ⟨⟨q, hq⟩, rfl⟩

theorem scalar_radius_core_volume_lower
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) {kappa t C : ℝ}
    (hnoncollapse : AncientKappaNoncollapsed K.flow kappa)
    (ht : t ≤ 0) (hC : C⁻¹ < kappa)
    {core : Set M} (radius : M → ℝ)
    (hr : ∀ y ∈ core, 0 < radius y)
    (hscalar : ∀ y ∈ core,
      scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
        ((K.flow.metric t).ball y (radius y)) = (radius y)⁻¹ ^ 2) :
    ∃ bound : ℝ, C⁻¹ < bound ∧ ∀ y ∈ core,
      ENNReal.ofReal (bound * radius y ^ 3) ≤
        calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball y (radius y)) := by
  exact ⟨kappa, hC, fun y hy =>
    scalar_radius_volume_lower P K hnoncollapse ht y (hr y hy) (hscalar y hy).le⟩

end PoincareConjecture
