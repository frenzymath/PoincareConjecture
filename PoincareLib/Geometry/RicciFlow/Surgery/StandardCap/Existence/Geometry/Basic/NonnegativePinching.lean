import PoincareLib.Geometry.RicciFlow.Pinching.Definitions

/-!
# The negative curvature part vanishes for nonnegative sectional curvature

Every actual orthonormal two-frame has nonnegative curvature value,
so the real infimum and its negative part have the required signs.
Source: Morgan-Tian Lemma 12.6 and Theorem 12.28, pp. 297-298, 323-324;
unit lifetime derivation, section 3.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M34

/-- Pointwise nonnegative sectional curvature makes the exact frozen
negative curvature part vanish (Lemma 12.6 and Theorem 12.28). -/
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

end PoincareMT.M34
