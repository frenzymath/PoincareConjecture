import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Chart
import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.LaplacianRegularity

/-!
# Tensor covariant derivatives in a tangent chart

This module records the exact coordinate-section formula for a covariant
tensor derivative. It keeps the ordinary derivative and every connection
correction term explicit, so coordinate parabolic consumers can use the
geometric operator without an assumed contact defect.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
  unfold TangentSpace
  infer_instance

/-- Exact first covariant derivative formula after evaluating all tensor slots
on coordinate-constant tangent fields. -/
theorem tensorCoordinateDerivative_formula (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (p : M)
    {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet)
    (u : TangentSpace (𝓡 n) x)
    (a : Fin k → EuclideanSpace ℝ (Fin n)) :
    D.covariantTensorDerivative T x
      (Fin.cons u (fun i => constantCoordinateField p (a i) x)) =
      mvfderiv (𝓡 n)
        (fun y => T y (fun i => constantCoordinateField p (a i) y)) x u -
      ∑ i, T x (Function.update
        (fun j => constantCoordinateField p (a j) x) i
        (D.connection (constantCoordinateField p (a i)) x u)) := by
  apply D.covariantTensorDerivative_on_fields hT
  intro i
  exact (contMDiffAt_constantCoordinateField p (a i) hx).mdifferentiableAt (by simp)

/-- The derivative formula is compatible with chart differentiation of the
coordinate representative of each evaluated tensor section. -/
theorem tensorCoordinateDerivative_chart_formula (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (p : M)
    {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet)
    (u : TangentSpace (𝓡 n) x)
    (a : Fin k → EuclideanSpace ℝ (Fin n)) :
    D.covariantTensorDerivative T x
      (Fin.cons u (fun i => constantCoordinateField p (a i) x)) =
      fderiv ℝ
        (fun z => T ((extChartAt (𝓡 n) p).symm z)
          (fun i => constantCoordinateField p (a i) ((extChartAt (𝓡 n) p).symm z)))
        (extChartAt (𝓡 n) p x)
        ((trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ x u) -
      ∑ i, T x (Function.update
        (fun j => constantCoordinateField p (a j) x) i
        (D.connection (constantCoordinateField p (a i)) x u)) := by
  rw [D.tensorCoordinateDerivative_formula hT p hx u a]
  congr 1
  apply mvfderiv_eq_chart_fderiv p
  · simpa using hx
  · apply hT.mdifferentiableAt_apply
    intro i
    exact (contMDiffAt_constantCoordinateField p (a i) hx).mdifferentiableAt (by simp)


/-- Lifting the actual connection coefficient recovers differentiation of
coordinate-constant fields, including all local frame derivatives. -/
lemma constantCoordinateField_connectionCoefficient (D : LeviCivitaData g) (p : M)
    {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet)
    (u v : EuclideanSpace ℝ (Fin n)) :
    constantCoordinateField p (D.coordinateConnectionCoefficient p x u v) x =
      D.connection (constantCoordinateField p v) x (constantCoordinateField p u x) := by
  rw [D.coordinateConnectionCoefficient_apply p hx]
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  exact e.symmL_continuousLinearMapAt hx _

/-- Raw tensor evaluation in the actual tangent trivialization. -/
def tensorCoordinateEvaluation {k : ℕ} (p : M) (T : CovariantTensorEvaluation n M k)
    (x : M) (a : Fin k → EuclideanSpace ℝ (Fin n)) : ℝ :=
  T x (fun i => constantCoordinateField p (a i) x)

/-- The induced covariant tensor connection has one negative connection
coefficient contribution for each covariant slot. -/
theorem tensorCoordinateDerivative_eq_fderiv_sub (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (p : M)
    {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet)
    (u : EuclideanSpace ℝ (Fin n)) (a : Fin k → EuclideanSpace ℝ (Fin n)) :
    tensorCoordinateEvaluation p (D.covariantTensorDerivative T) x (Fin.cons u a) =
      fderiv ℝ (fun z => tensorCoordinateEvaluation p T
        ((extChartAt (𝓡 n) p).symm z) a) (extChartAt (𝓡 n) p x) u -
        ∑ i, tensorCoordinateEvaluation p T x
          (Function.update a i (D.coordinateConnectionCoefficient p x u (a i))) := by
  have hcons : (fun i : Fin (k + 1) => constantCoordinateField p
      ((Fin.cons u a : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) i) x) =
      Fin.cons (constantCoordinateField p u x) (fun i => constantCoordinateField p (a i) x) := by
    ext i
    cases i using Fin.cases <;> rfl
  have hcoord := coordinateRepresentative_constant p u hx
  have hcoord' : (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ x
      (constantCoordinateField p u x) = u := hcoord
  unfold tensorCoordinateEvaluation
  rw [hcons, D.tensorCoordinateDerivative_chart_formula hT p hx, hcoord']
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← D.constantCoordinateField_connectionCoefficient p hx]
  congr 1
  ext j
  by_cases h : j = i <;> simp [h, Function.update_of_ne]

end PoincareMT.LeviCivitaData
