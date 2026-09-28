import PoincareConjecture.Proofs.M12.LinearAlgebra.BilinearForm.Trace
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Harnack.TwoForm
import PoincareConjecture.Definitions.Ch04.Harnack










open scoped BigOperators

namespace Poincare.Geometry.Curvature.Operator

variable {I : Type*} [Fintype I] [DecidableEq I]


noncomputable def halfWedge (v : I → ℝ) (a i j : I) : ℝ :=
  (v i * (if j = a then 1 else 0) -
    (if i = a then 1 else 0) * v j) / 2

theorem curvature_operator_ricci_trace
    (Rm : I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (hfirst : ∀ i j k l, Rm i j k l = -Rm j i k l)
    (hlast : ∀ i j k l, Rm i j k l = -Rm i j l k)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l)
    (v : I → ℝ)
    (hoperator : ∀ A : I → I → ℝ, (∀ i j, A i j = -A j i) →
      0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, Rm i j k l * A i j * A k l) :
    0 ≤ ∑ i, ∑ k, Ric i k * v i * v k := by
  classical
  have hA (a : I) :
      ∀ i j, halfWedge v a i j = -halfWedge v a j i := by
    intro i j
    simp only [halfWedge]
    split_ifs <;> ring
  have hnonneg (a : I) :
      0 ≤ ∑ i, ∑ j, ∑ k, ∑ l,
        Rm i j k l * halfWedge v a i j * halfWedge v a k l := by
    exact hoperator (halfWedge v a) (hA a)
  have htrace := Finset.sum_nonneg (s := Finset.univ)
    (fun a _ => hnonneg a)
  have hcontract :=
    Poincare.RicciFlow.Harnack.curvature_contraction_half_wedge_trace
      Rm Ric hfirst hlast hRic v
  rw [← hcontract]
  simpa [halfWedge] using htrace

theorem ricci_bounds_of_nonnegative_operator
    (Rm : I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (hfirst : ∀ i j k l, Rm i j k l = -Rm j i k l)
    (hlast : ∀ i j k l, Rm i j k l = -Rm i j l k)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l)
    (v : I → ℝ)
    (hoperator : ∀ A : I → I → ℝ, (∀ i j, A i j = -A j i) →
      0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, Rm i j k l * A i j * A k l) :
    0 ≤ ∑ i, ∑ k, Ric i k * v i * v k ∧
      (∑ i, ∑ k, Ric i k * v i * v k) ≤
        (∑ i, Ric i i) * ∑ i, (v i) ^ 2 := by
  have hnonneg := curvature_operator_ricci_trace Rm Ric hfirst hlast hRic v hoperator
  have hquad : ∀ w : I → ℝ, 0 ≤ ∑ i, ∑ k, Ric i k * w i * w k := by
    intro w
    exact curvature_operator_ricci_trace Rm Ric hfirst hlast hRic w hoperator
  exact ⟨hnonneg,
    Poincare.LinearAlgebra.quadratic_le_trace_mul_sum_sq Ric hquad v⟩

end Poincare.Geometry.Curvature.Operator
