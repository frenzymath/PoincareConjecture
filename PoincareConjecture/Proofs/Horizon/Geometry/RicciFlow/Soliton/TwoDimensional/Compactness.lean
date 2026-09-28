import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Conservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.ScalarBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Myers.Compact

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace LeviCivitaData

variable [PreconnectedSpace M] {g : RiemannianMetric 2 M}

theorem compactSpace_of_surface_shrinker (D : LeviCivitaData g)
    (hc : MetricComplete g) {f : M → ℝ} {lambda : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f) (hlambda : 0 < lambda)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hoperator : ∀ x : M, D.NonnegativeCurvatureOperator x)
    (hnonflat : ∃ x : M, D.curvatureTensorNorm x ≠ 0) :
    CompactSpace M := by
  obtain ⟨A, C, hA, hC⟩ := D.exists_conservation_constants_of_surface_soliton hf hsol
  obtain ⟨k, hk, hRic⟩ := D.ricci_lower_bound_of_surface_conservation f (2 * lambda)
    (mul_pos (by norm_num) hlambda) hoperator hnonflat A C hA hC
  exact g.compactSpace_of_positive_ricci D hc hk hRic

end LeviCivitaData

namespace GradientShrinkingSolitonData

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem compactSpace (S : GradientShrinkingSolitonData 2 M) : CompactSpace M := by
  exact S.connection.compactSpace_of_surface_shrinker S.complete S.potential_C2
    (by norm_num : (0 : ℝ) < 1 / 2) S.soliton_equation S.nonnegative_curvature S.nonflat

end GradientShrinkingSolitonData

end PoincareConjecture
