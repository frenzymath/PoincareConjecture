import PoincareLib.Geometry.Riemannian.Curvature.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/Ch01/TensorOperators.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/


/-!
# Covariant tensor evaluations and differential operators

The Leibniz formula uses fixed local extensions at each differentiation point.
These are complete expressions on raw evaluations. Their tensor interpretation
requires the separately stated regularity and independence obligations.
See Morgan-Tian, printed pp. 3-8, and reviews/contracts/tensor-operators-v1.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT

/-- Raw scalar evaluations on k tangent inputs; no multilinearity is built into the type. -/
abbrev CovariantTensorEvaluation (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (k : ℕ) :=
  (x : M) → (Fin k → TangentSpace (𝓡 n) x) → ℝ

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric

/-- Full component norm in the chosen metric's pointwise orthonormal basis. -/
noncomputable def tensorNorm (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
    (T x (fun i ↦ b (a i))) ^ 2)

end RiemannianMetric

namespace LeviCivitaData

variable {g : RiemannianMetric n M}

/-- Covariant differentiation with the derivative input first and all input corrections. -/
noncomputable def covariantTensorDerivative (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) : CovariantTensorEvaluation n M (k + 1) :=
  fun x v ↦
    mvfderiv (𝓡 n)
      (fun y ↦ T y (fun i ↦
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) x (v 0) -
    ∑ i, T x (Function.update (fun j ↦ v j.succ) i
      (D.connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ)) x (v 0)))

/-- Repeated covariant differentiation, including corrections for previous derivative slots. -/
noncomputable def iteratedCovariantTensorDerivative (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) :
    (m : ℕ) → CovariantTensorEvaluation n M (k + m)
  | 0 => T
  | m + 1 => D.covariantTensorDerivative (D.iteratedCovariantTensorDerivative T m)

/-- The metric trace in the two derivative inputs of the second covariant derivative. -/
noncomputable def tensorLaplacian (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) : CovariantTensorEvaluation n M k :=
  fun x v ↦
    let b := g.orthonormalBasis x
    ∑ i, D.iteratedCovariantTensorDerivative T 2 x (Fin.cons (b i) (Fin.cons (b i) v))

/-- The existing four-covariant curvature evaluation with tuple inputs. -/
noncomputable def riemannEvaluation (D : LeviCivitaData g) :
    CovariantTensorEvaluation n M 4 :=
  fun x v ↦ D.curvatureTensor x (v 0) (v 1) (v 2) (v 3)

/-- The existing covariant Ricci evaluation with tuple inputs. -/
noncomputable def ricciEvaluation (D : LeviCivitaData g) :
    CovariantTensorEvaluation n M 2 :=
  fun x v ↦ D.ricci x (v 0) (v 1)

/-- Full norm of the m-th covariant derivative of the actual curvature tensor. -/
noncomputable def curvatureDerivativeNorm (D : LeviCivitaData g) (m : ℕ)
    (x : M) : ℝ :=
  g.tensorNorm (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) x

/-- Nonnegative sectional curvature, expressed without dividing by a Gram determinant. -/
def NonnegativeSectionalCurvature (D : LeviCivitaData g) : Prop :=
  ∀ (x : M) (v w : TangentSpace (𝓡 n) x), 0 ≤ D.curvatureTensor x v w v w

/-- Nonnegative Ricci curvature as an actual quadratic-form inequality. -/
def NonnegativeRicciCurvature (D : LeviCivitaData g) : Prop :=
  ∀ (x : M) (v : TangentSpace (𝓡 n) x), 0 ≤ D.ricci x v v

end LeviCivitaData

end PoincareMT
