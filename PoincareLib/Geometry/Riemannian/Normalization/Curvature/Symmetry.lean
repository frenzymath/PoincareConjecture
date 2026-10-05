import PoincareLib.Geometry.Riemannian.Curvature.Basic
import Mathlib.Tactic.Abel

/-!
# Antisymmetry in the first two curvature slots

These algebraic identities implement the first-slot symmetry from Morgan-Tian,
Claim 1.5, printed p. 6. The field identity needs no regularity hypothesis.
They do not establish tensoriality or the other curvature symmetries.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Swapping the first two fields negates the curvature commutator. -/
theorem normalization_curvatureOnFields_swap (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    D.curvatureOnFields Y X Z x = -D.curvatureOnFields X Y Z x := by
  unfold curvatureOnFields
  rw [VectorField.mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  abel

/-- Pointwise curvature is antisymmetric in its first two slots. -/
theorem normalization_curvature_swap (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x v u w = -D.curvature x u v w :=
  D.normalization_curvatureOnFields_swap
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x

end PoincareMT.LeviCivitaData
