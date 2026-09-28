import PoincareConjecture.Definitions.Ch04.Pinching










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M34



theorem negativeCurvaturePart_eq_zero_of_nonnegativeSectionalAt
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M)
    (h : ∀ v w : TangentSpace (𝓡 3) x, 0 ≤ D.curvatureTensor x v w v w) :
    D.negativeCurvaturePart x = 0 := by
  have hleast : 0 ≤ D.leastSectionalCurvature x := by
    apply Real.sInf_nonneg
    rintro _ ⟨v, w, _, rfl⟩
    exact h v w
  exact max_eq_right (neg_nonpos.mpr hleast)

end PoincareConjecture.M34
