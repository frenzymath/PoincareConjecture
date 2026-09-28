import PoincareConjecture.Definitions.Ch01.TensorOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureDerivativeNorm_zero {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) :
    D.curvatureDerivativeNorm 0 x = D.curvatureTensorNorm x := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let e : (Fin 4 → Fin d) ≃ (Fin d × Fin d × Fin d × Fin d) :=
    { toFun := fun a ↦ (a 0, a 1, a 2, a 3)
      invFun := fun p ↦ ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := by
        intro a
        funext i
        fin_cases i <;> rfl
      right_inv := by
        rintro ⟨i, j, k, l⟩
        rfl }
  change Real.sqrt (∑ a : Fin 4 → Fin d,
      (D.curvatureTensor x (b (a 0)) (b (a 1)) (b (a 2)) (b (a 3))) ^ 2) =
    Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
      (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2)
  congr 1
  calc
    (∑ a : Fin 4 → Fin d,
        (D.curvatureTensor x (b (a 0)) (b (a 1)) (b (a 2)) (b (a 3))) ^ 2) =
        ∑ p : Fin d × Fin d × Fin d × Fin d,
          (D.curvatureTensor x (b p.1) (b p.2.1) (b p.2.2.1) (b p.2.2.2)) ^ 2 := by
      apply Fintype.sum_equiv e
      intro a
      rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2 := by
      simp only [Fintype.sum_prod_type]
      rfl

end PoincareConjecture.LeviCivitaData
