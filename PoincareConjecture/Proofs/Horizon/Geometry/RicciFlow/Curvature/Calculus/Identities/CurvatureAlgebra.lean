import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureOnFields_swap (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    D.curvatureOnFields Y X Z x = -D.curvatureOnFields X Y Z x := by
  unfold LeviCivitaData.curvatureOnFields
  rw [VectorField.mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  abel

theorem curvature_swap (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x v u w = -D.curvature x u v w :=
  curvatureOnFields_swap D
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x

theorem curvature_self (D : LeviCivitaData g) (x : M)
    (u w : TangentSpace (𝓡 n) x) : D.curvature x u u w = 0 := by
  simp [LeviCivitaData.curvature, LeviCivitaData.curvatureOnFields]

theorem curvatureTensor_swap_first (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x v u w z = -D.curvatureTensor x u v w z := by
  unfold LeviCivitaData.curvatureTensor
  rw [curvature_swap D]
  simp only [map_neg, neg_apply]

end PoincareConjecture.RicciFlowAnalysis
