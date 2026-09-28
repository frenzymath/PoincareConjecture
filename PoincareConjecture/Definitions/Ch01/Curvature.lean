import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.InnerProductSpace.PiL2










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric


noncomputable def orthonormalBasis (g : RiemannianMetric n M) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)))
      ℝ (TangentSpace (𝓡 n) x) :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  stdOrthonormalBasis ℝ (TangentSpace (𝓡 n) x)

end RiemannianMetric

namespace LeviCivitaData

variable {g : RiemannianMetric n M}


noncomputable def curvatureOnFields (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    TangentSpace (𝓡 n) x :=
  D.connection (fun y ↦ D.connection Z y (Y y)) x (X x) -
    D.connection (fun y ↦ D.connection Z y (X y)) x (Y x) -
    D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x)


noncomputable def curvature (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) : TangentSpace (𝓡 n) x :=
  D.curvatureOnFields
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x


noncomputable def curvatureTensor (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) : ℝ :=
  g.inner x (D.curvature x u v z) w


noncomputable def ricci (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, D.curvatureTensor x u (b i) v (b i)


noncomputable def scalarCurvature (D : LeviCivitaData g) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, D.ricci x (b i) (b i)


noncomputable def sectionalCurvature (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  D.curvatureTensor x u v u v /
    (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)


noncomputable def curvatureTensorNorm (D : LeviCivitaData g) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
    (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2)

end LeviCivitaData

end PoincareConjecture
