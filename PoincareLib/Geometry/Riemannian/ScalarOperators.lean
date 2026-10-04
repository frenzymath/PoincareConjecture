import PoincareLib.Geometry.Riemannian.Curvature.Basic

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/Ch01/ScalarOperators.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/


/-!
# Scalar differential operators and Ricci squared norm

The Hessian and its metric trace follow Morgan-Tian, printed pp. 4-5.
Their geometric use requires regular germs. The Ricci squared norm is the
full sum of squares used in the scalar evolution equation on printed p. 41.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The scalar Hessian on fields, totalized by Mathlib outside regular germs. -/
noncomputable def hessianOnFields (D : LeviCivitaData g) (f : M → ℝ)
    (X Y : (x : M) → TangentSpace (𝓡 n) x) (x : M) : ℝ :=
  mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x (X x) -
    mvfderiv (𝓡 n) f x (D.connection Y x (X x))

/-- The pointwise Hessian using two fixed locally smooth extensions based at `x`. -/
noncomputable def hessian (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  D.hessianOnFields f
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x

/-- The metric trace of the Hessian, with the nonnegative-at-minima sign convention. -/
noncomputable def laplacian (D : LeviCivitaData g) (f : M → ℝ) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, D.hessian f x (b i) (b i)

/-- The full covariant Ricci squared norm in the chosen metric's orthonormal basis. -/
noncomputable def ricciNormSq (D : LeviCivitaData g) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2

end PoincareMT.LeviCivitaData
