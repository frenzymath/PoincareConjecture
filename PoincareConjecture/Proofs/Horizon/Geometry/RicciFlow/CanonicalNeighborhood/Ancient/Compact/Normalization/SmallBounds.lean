import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.CarrierLift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Noncollapse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace M26CanonicalNeighborhoodPredecessors

theorem scalar_pos_small (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (t : ℝ) (ht : t ≤ 0) (x : M) :
    0 < (K.flow.connection t).scalarCurvature x := by
  obtain ⟨N⟩ := P.normalization (ULift.{u} M) K.ulift (ULift.up x) t ht
  have hpos := N.scale_eq ▸ N.scale_pos
  simpa only [AncientKappaSolution.ulift_scalarCurvature] using hpos

theorem past_norm_le_scalar_small (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (t b : ℝ) (htb : t ≤ b) (hb : b ≤ 0) (x : M) :
    (K.flow.connection t).curvatureTensorNorm x ≤
      (K.flow.connection b).scalarCurvature x := by
  simpa only [AncientKappaSolution.ulift_curvatureTensorNorm,
    AncientKappaSolution.ulift_scalarCurvature] using
      P.past_norm_le_scalar (ULift.{u} M) K.ulift t b htb hb (ULift.up x)

end M26CanonicalNeighborhoodPredecessors

theorem scalar_radius_volume_lower_small
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
  apply (P.past_norm_le_scalar_small K s t hs.2 ht q).trans
  apply le_trans ?_ hscalar
  exact le_csSup (K.scalar_range_ball_bddAbove ht p r) ⟨⟨q, hq⟩, rfl⟩

end PoincareConjecture
