import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceScalarRealization
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceScalarAccuracy
import PoincareConjecture.Proofs.M34.Standard.NeckHeightControl
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem capPersistence_exists_neck_scalar_accuracy {eta : ℝ} (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace E₃ M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g), N.epsilon < delta0 →
        (∀ x ∈ N.carrier, |N.scale ^ 2 * N.connection.scalarCurvature x - 1| < eta) ∧
        (∀ x ∈ closure N.carrier,
          |N.scale ^ 2 * N.connection.scalarCurvature x - 1| ≤ eta) := by
  obtain ⟨delta0, hdelta0, haccuracy⟩ := capPersistence_exists_scalar_accuracy heta
  refine ⟨delta0, hdelta0, ?_⟩
  intro M _ _ _ _ g N hN
  have hpoint (q : UnitTwoSphere) (s : ℝ)
      (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
      |N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, s)) - 1| < eta := by
    obtain ⟨gE, DE, V, hV, h0, hdom, hcoeff, hscalar⟩ :=
      N.exists_capPersistence_metric_germ q s hs
    apply (show |DE.scalarCurvature 0 - 1| < eta → _ from fun h => by
      rwa [hscalar] at h)
    apply haccuracy N.epsilon N.epsilon_pos hN
      (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
      N.metric_comparison.close q s hs gE DE
    intro a b
    filter_upwards [hV.mem_nhds h0] with x hx
    have hc := congrArg (fun A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) (hcoeff x hx)
    exact hc.trans (N.capPersistenceEuclideanMap_coefficient q s (hdom x hx) a b)
  have hcarrier : ∀ x ∈ N.carrier,
      |N.scale ^ 2 * N.connection.scalarCurvature x - 1| < eta := by
    intro x hx
    have h := hpoint (N.coordinate_inverse x).1 (N.coordinate_inverse x).2
      (N.coordinate_inverse_mem x hx).2
    rwa [N.coordinate_map_inverse_eq hx] at h
  refine ⟨hcarrier, ?_⟩
  have hc : Continuous (fun x => |N.scale ^ 2 * N.connection.scalarCurvature x - 1|) :=
    ((continuous_const.mul (contMDiff_scalarCurvature N.connection).continuous).sub
      continuous_const).abs
  exact closure_minimal (fun x hx => (hcarrier x hx).le)
    (isClosed_le hc continuous_const)

end PoincareConjecture.M34
