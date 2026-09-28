import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Ambient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.EuclideanModel










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_ambient_curvature_control {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ ε₀ →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        |N.scale ^ 2 * D.scalarCurvature (N.coordinate_map (q, s)) - 1| < α ∧
        ∀ i j : Fin 3,
          |D.ricci (N.centeredEuclideanParametrization q s 0)
              (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0
                (roundCylinderEuclideanBasis i))
              (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0
                (roundCylinderEuclideanBasis j)) -
            (if i = j ∧ i ≠ 2 then 1 else 0)| < α := by
  obtain ⟨ε₀, hε₀, hε₀small, hcontrol⟩ :=
    exists_normalizedEuclideanCoefficients_curvature_control.{u} hα
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hε q s hs
  obtain ⟨h, Dh, heq, hscalar, hricci⟩ := hcontrol N hε q hs
  obtain ⟨hscalar_eq, hricci_eq⟩ := N.normalized_realization_curvature D q hs Dh heq
  refine ⟨?_, fun i j => ?_⟩
  · simpa only [hscalar_eq, roundCylinderEuclideanMetric_scalarCurvature] using hscalar
  · simpa only [hricci_eq, roundCylinderEuclideanMetric_ricci_zero_basis] using hricci i j

end PoincareConjecture.EpsilonNeck
