import PoincareConjecture.Definitions.Ch01.Curvature
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

abbrev CovariantTensorEvaluation (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (k : ℕ) :=
  (x : M) → (Fin k → TangentSpace (𝓡 n) x) → ℝ

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric

noncomputable def tensorNorm (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
    (T x (fun i ↦ b (a i))) ^ 2)

end RiemannianMetric

namespace LeviCivitaData

variable {g : RiemannianMetric n M}

noncomputable def covariantTensorDerivative (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) : CovariantTensorEvaluation n M (k + 1) :=
  fun x v ↦
    mvfderiv (𝓡 n)
      (fun y ↦ T y (fun i ↦
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) x (v 0) -
    ∑ i, T x (Function.update (fun j ↦ v j.succ) i
      (D.connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ)) x (v 0)))

noncomputable def iteratedCovariantTensorDerivative (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) :
    (m : ℕ) → CovariantTensorEvaluation n M (k + m)
  | 0 => T
  | m + 1 => D.covariantTensorDerivative (D.iteratedCovariantTensorDerivative T m)

noncomputable def tensorLaplacian (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) : CovariantTensorEvaluation n M k :=
  fun x v ↦
    let b := g.orthonormalBasis x
    ∑ i, D.iteratedCovariantTensorDerivative T 2 x (Fin.cons (b i) (Fin.cons (b i) v))

noncomputable def riemannEvaluation (D : LeviCivitaData g) :
    CovariantTensorEvaluation n M 4 :=
  fun x v ↦ D.curvatureTensor x (v 0) (v 1) (v 2) (v 3)

noncomputable def ricciEvaluation (D : LeviCivitaData g) :
    CovariantTensorEvaluation n M 2 :=
  fun x v ↦ D.ricci x (v 0) (v 1)

noncomputable def curvatureDerivativeNorm (D : LeviCivitaData g) (m : ℕ)
    (x : M) : ℝ :=
  g.tensorNorm (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) x

def NonnegativeSectionalCurvature (D : LeviCivitaData g) : Prop :=
  ∀ (x : M) (v w : TangentSpace (𝓡 n) x), 0 ≤ D.curvatureTensor x v w v w

def NonnegativeRicciCurvature (D : LeviCivitaData g) : Prop :=
  ∀ (x : M) (v : TangentSpace (𝓡 n) x), 0 ≤ D.ricci x v v

end LeviCivitaData

end PoincareConjecture
