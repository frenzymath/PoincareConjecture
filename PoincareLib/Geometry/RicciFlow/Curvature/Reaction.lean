import PoincareLib.Geometry.Riemannian.Tensor.Operations

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/Ch03/CurvatureReaction.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/


/-!
# Fixed-input curvature reactions

Morgan-Tian equation (3.5) and the corrected contraction in (3.6), printed p. 41.
The four-covariant convention is g(R(u,v)z,w). The Ricci index correction is
recorded in reviews/errata/2026-09-11-tensor-evolution.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The quadratic B contraction in the covariant curvature evolution equation. -/
noncomputable def curvatureB (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) *
    D.curvatureTensor x w (b i) z (b j)

/-- Reaction for four-covariant curvature on fixed tangent inputs. -/
noncomputable def curvatureReaction (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  2 * (D.curvatureB x u v w z - D.curvatureB x u v z w -
    D.curvatureB x u z v w + D.curvatureB x u w v z) -
    ∑ i, (D.ricci x u (b i) * D.curvatureTensor x (b i) v w z +
      D.ricci x v (b i) * D.curvatureTensor x u (b i) w z +
      D.ricci x w (b i) * D.curvatureTensor x u v (b i) z +
      D.ricci x z (b i) * D.curvatureTensor x u v w (b i))

/-- Corrected covariant Ricci reaction, using the book's positive-sphere convention. -/
noncomputable def ricciReaction (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  2 * (∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) * D.ricci x (b i) (b j)) -
    2 * (∑ i, D.ricci x u (b i) * D.ricci x (b i) v)

end PoincareMT.LeviCivitaData
