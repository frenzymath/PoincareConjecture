import PoincareConjecture.Proofs.M25.AppA_1_Necks.AmbientRicci
import PoincareConjecture.Proofs.M25.AppA_1_Necks.ModelRicci
import PoincareConjecture.Proofs.M25.AppA_1_Necks.RealizedRicciQuadratic

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_normalized_ricci_basis_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ i j : Fin 3,
      |N.connection.ricci (N.coordinate_map (q, s))
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0 (m25_roundCylinderEuclideanBasis i))
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0
          (m25_roundCylinderEuclideanBasis j)) -
        (if i = j ∧ i ≠ 2 then 1 else 0)| < α := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ := exists_realized_scalar_ricci_control.{u} hα
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N hepsilon q s hs i j
  obtain ⟨h, D, V, hV, h0, hstrip, heq⟩ :=
    N.m25_exists_normalizedEuclideanCoefficients_realization q hs
  have hnear : h.euclideanCoefficients =ᶠ[𝓝 0] N.m25_normalizedEuclideanCoefficients q s :=
    Filter.mem_of_superset (hV.mem_nhds h0) heq
  have hricci := (hcontrol N hepsilon q hs h D hnear).2 i j
  rw [N.realization_ricci_eq q s h D hV h0 hstrip heq,
    roundCylinderEuclideanModelConnection_ricci_zero_basis] at hricci
  exact hricci

theorem exists_normalized_ricci_quadratic_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ v : EuclideanSpace ℝ (Fin 3),
      |N.connection.ricci (N.coordinate_map (q, s))
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0 v)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0 v) -
        ‖((RiemannianMetric.lineModelEquiv 2).symm v).1‖ ^ 2| ≤ α * ‖v‖ ^ 2 := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ := exists_realized_ricci_quadratic_control.{u} hα
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N hepsilon q s hs v
  obtain ⟨h, D, V, hV, h0, hstrip, heq⟩ :=
    N.m25_exists_normalizedEuclideanCoefficients_realization q hs
  have hnear : h.euclideanCoefficients =ᶠ[𝓝 0] N.m25_normalizedEuclideanCoefficients q s :=
    Filter.mem_of_superset (hV.mem_nhds h0) heq
  have hricci := hcontrol N hepsilon q hs h D hnear v
  rw [N.realization_ricci_eq q s h D hV h0 hstrip heq,
    roundCylinderEuclideanModelConnection_ricci_zero_self] at hricci
  exact hricci

end PoincareConjecture.EpsilonNeck
