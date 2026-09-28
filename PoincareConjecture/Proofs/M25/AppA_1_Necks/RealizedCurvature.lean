import PoincareConjecture.Proofs.M25.AppA_1_Necks.GermRealization
import PoincareConjecture.Proofs.M25.AppA_1_Necks.ModelMetric
import PoincareConjecture.Proofs.M25.AppA_1_Necks.CurvatureContinuity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_realized_scalar_ricci_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData h),
      h.euclideanCoefficients =ᶠ[𝓝 0] N.m25_normalizedEuclideanCoefficients q s →
      |D.scalarCurvature 0 - roundCylinderEuclideanModelConnection.scalarCurvature 0| < α ∧
        ∀ i j : Fin 3,
        |D.ricci 0 (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j) -
          roundCylinderEuclideanModelConnection.ricci 0
            (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j)| < α := by
  obtain ⟨C, hC, hjets⟩ := exists_normalizedEuclideanMetric_scalar_twoJet_bound.{u}
  obtain ⟨delta, hdelta, hmodulus⟩ :=
    roundCylinderEuclideanModelConnection.m25_exists_scalar_ricci_control_of_metric_twoJet
      0 m25_roundCylinderEuclideanBasis hα
  refine ⟨min (1 / 200) (delta / (2 * C)),
    lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro M _ _ _ _ _ _ g N hepsilon q s hs h D heq
  have hepsilon' : N.epsilon ≤ delta / (2 * C) :=
    hepsilon.trans (min_le_right _ _)
  have hjetSmall : C * N.epsilon < delta := by
    have h := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp hepsilon'
    nlinarith
  apply hmodulus h D
  intro r hr i j
  exact (hjets N q hs h heq r hr i j).trans_lt hjetSmall

end PoincareConjecture.EpsilonNeck
