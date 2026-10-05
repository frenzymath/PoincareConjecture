import PoincareLib.Geometry.Riemannian.Curvature.Basic
import Mathlib.Tactic.Abel

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M04/CurvatureAlgebra.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. See the curvature import record under
`references/ricci-flow/mapher/curvature/`. -/

/-!
# Elementary curvature antisymmetry

The connection commutator is antisymmetric in its first two inputs, even
before imposing regularity on its fields. Specializing to the retained
extensions gives the corresponding pointwise identities. These are the
first-pair identities for the convention of Morgan-Tian, printed pp. 5-7.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Swapping the two differentiating fields negates the curvature commutator. -/
theorem curvatureOnFields_swap (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    D.curvatureOnFields Y X Z x = -D.curvatureOnFields X Y Z x := by
  unfold LeviCivitaData.curvatureOnFields
  rw [VectorField.mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  abel

/-- The pointwise curvature is antisymmetric in its first two tangent inputs. -/
theorem curvature_swap (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x v u w = -D.curvature x u v w :=
  curvatureOnFields_swap D
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x

/-- Equal differentiating inputs give zero curvature. -/
theorem curvature_self (D : LeviCivitaData g) (x : M)
    (u w : TangentSpace (𝓡 n) x) : D.curvature x u u w = 0 := by
  simp [LeviCivitaData.curvature, LeviCivitaData.curvatureOnFields]

/-- Pairing with the metric preserves the first-pair antisymmetry. -/
theorem curvatureTensor_swap_first (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x v u w z = -D.curvatureTensor x u v w z := by
  unfold LeviCivitaData.curvatureTensor
  rw [curvature_swap D]
  simp only [map_neg, neg_apply]

end PoincareMT.RicciFlowAnalysis
