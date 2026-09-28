import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

theorem uniform_core_scalar_bounds_of_services
    (P : NoncompactKappaServices.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsCompact (Set.univ : Set M) →
        ∀ x ∈ (K.flow.metric 0).ball p
          (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
          C⁻¹ * (K.flow.connection 0).scalarCurvature p <
              (K.flow.connection 0).scalarCurvature x ∧
            (K.flow.connection 0).scalarCurvature x <
              C * (K.flow.connection 0).scalarCurvature p := by
  obtain ⟨C, hC, hupper⟩ := nonround_uniform_core_scalar_upper_of_services P hD
  have hCpos : 0 < C := zero_lt_one.trans hC
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnoncompact x hx
  have hnonround := K.not_isRound_of_noncompact hnoncompact
  have hpos (q : M) : 0 < (K.flow.connection 0).scalarCurvature q := by
    obtain ⟨N⟩ := P.normalization M K q 0 le_rfl
    exact N.scale_eq ▸ N.scale_pos
  refine ⟨?_, hupper K p hnonround x hx⟩
  have hreverse : (K.flow.connection 0).scalarCurvature p <
      C * (K.flow.connection 0).scalarCurvature x := by
    by_cases hxp : (K.flow.connection 0).scalarCurvature p ≤
        (K.flow.connection 0).scalarCurvature x
    · nlinarith [hpos x]
    · have hxple := (lt_of_not_ge hxp).le
      have hscale := Real.rpow_le_rpow_of_nonpos (hpos x) hxple
        (by norm_num : (-1 / 2 : ℝ) ≤ 0)
      have hp : p ∈ (K.flow.metric 0).ball x
          (D * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)) := by
        have hdist : (K.flow.metric 0).edist x p = (K.flow.metric 0).edist p x := by
          let := RiemannianMetric.toMetricSpace (K.flow.metric 0)
          exact edist_comm x p
        change (K.flow.metric 0).edist x p < _
        rw [hdist]
        exact hx.trans_le (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hscale hD.le))
      exact hupper K x hnonround p hp
  have hdivide := (div_lt_iff₀ hCpos).mpr (by simpa only [mul_comm] using hreverse)
  simpa only [div_eq_mul_inv, mul_comm] using hdivide

theorem uniform_core_scalar_bounds
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsCompact (Set.univ : Set M) →
        ∀ x ∈ (K.flow.metric 0).ball p
          (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
          C⁻¹ * (K.flow.connection 0).scalarCurvature p <
              (K.flow.connection 0).scalarCurvature x ∧
            (K.flow.connection 0).scalarCurvature x <
              C * (K.flow.connection 0).scalarCurvature p := by
  exact uniform_core_scalar_bounds_of_services P.noncompactServices hD

end PoincareConjecture.NoncompactKappa.Positive
