import PoincareConjecture.Definitions.Ch01.Curvature
import Mathlib.Tactic.Abel









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem curvatureOnFields_swap (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    D.curvatureOnFields Y X Z x = -D.curvatureOnFields X Y Z x := by
  unfold curvatureOnFields
  rw [VectorField.mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  abel


theorem curvature_swap (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x v u w = -D.curvature x u v w :=
  D.curvatureOnFields_swap
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x

end PoincareConjecture.LeviCivitaData
