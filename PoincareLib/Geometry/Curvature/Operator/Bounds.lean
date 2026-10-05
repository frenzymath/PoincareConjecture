import PoincareLib.LinearAlgebra.BilinearForm.Trace
import PoincareLib.Geometry.RicciFlow.Harnack.TwoForm
import PoincareLib.Geometry.Riemannian.Curvature.Basic

/-!
# Ricci bounds from a nonnegative curvature operator

The M06 curvature operator is the frozen finite sum over skew coefficient
arrays. Evaluating it on half-wedges and tracing in the orthonormal frame
gives the Ricci quadratic form. The final trace estimate is a finite
positive-quadratic-form argument and does not use a diagonalisation theorem.
-/

open scoped BigOperators

namespace Poincare.Geometry.Curvature.Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The elementary half-wedge coefficients used to test the curvature operator. -/
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

namespace PoincareMT

open scoped Manifold ContDiff Bundle BigOperators

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

namespace LeviCivitaData

/-- A skew coefficient array in the pointwise orthonormal frame. -/
def IsSkewCoefficient (d : ℕ) (A : Fin d → Fin d → ℝ) : Prop :=
  ∀ i j, A i j = -A j i

/-- The finite-sum curvature-operator quadratic form from the frozen M06 contract. -/
noncomputable def curvatureOperatorQuadratic (D : LeviCivitaData g)
    (x : M) (A : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, ∑ j, ∑ k, ∑ l,
    A i j * A k l * D.curvatureTensor x (b i) (b j) (b k) (b l)

/-- Nonnegative curvature operator, quantified over all skew arrays. -/
def NonnegativeCurvatureOperator (D : LeviCivitaData g) (x : M) : Prop :=
  ∀ A, IsSkewCoefficient (Module.finrank ℝ (TangentSpace (𝓡 n) x)) A →
    0 ≤ D.curvatureOperatorQuadratic x A

/-- The pointwise curvature-operator bound from the frozen M06 contract. -/
def CurvatureOperatorBound (D : LeviCivitaData g)
    (K : ℝ) (x : M) : Prop :=
  ∀ A, IsSkewCoefficient (Module.finrank ℝ (TangentSpace (𝓡 n) x)) A →
    |D.curvatureOperatorQuadratic x A| ≤
      K * ∑ i, ∑ j, (A i j) ^ 2

end LeviCivitaData
end PoincareMT
