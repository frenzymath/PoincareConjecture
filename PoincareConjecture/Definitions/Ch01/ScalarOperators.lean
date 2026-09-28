import PoincareConjecture.Definitions.Ch01.Curvature









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


noncomputable def hessianOnFields (D : LeviCivitaData g) (f : M → ℝ)
    (X Y : (x : M) → TangentSpace (𝓡 n) x) (x : M) : ℝ :=
  mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x (X x) -
    mvfderiv (𝓡 n) f x (D.connection Y x (X x))


noncomputable def hessian (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  D.hessianOnFields f
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x


noncomputable def laplacian (D : LeviCivitaData g) (f : M → ℝ) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, D.hessian f x (b i) (b i)


noncomputable def ricciNormSq (D : LeviCivitaData g) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2

end PoincareConjecture.LeviCivitaData
