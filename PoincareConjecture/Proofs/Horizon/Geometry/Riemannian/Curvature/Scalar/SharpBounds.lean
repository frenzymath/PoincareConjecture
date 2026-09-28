import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.NormBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Reaction
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace Poincare.LinearAlgebra

private theorem entry_sq_le_diagonal_mul {I : Type*} [Fintype I]
    (B : I → I → ℝ) (hsym : ∀ i j, B i j = B j i)
    (hB : ∀ v : I → ℝ, 0 ≤ ∑ i, ∑ j, B i j * v i * v j) (i j : I) :
    (B i j) ^ 2 ≤ B i i * B j j := by
  classical
  have hquad (t : ℝ) : 0 ≤ B i i * (t * t) + (2 * B i j) * t + B j j := by
    have h := hB (fun k => (if k = i then t else 0) + (if k = j then 1 else 0))
    simp only [mul_add, add_mul, Finset.sum_add_distrib] at h
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [← hsym i j] at h
    nlinarith
  have h := discrim_le_zero hquad
  unfold discrim at h
  nlinarith

end Poincare.LinearAlgebra

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 800000 in

theorem abs_scalarCurvature_le_curvatureTensorNorm_sharp
    (D : LeviCivitaData g) (x : M) :
    |D.scalarCurvature x| ≤ (n : ℝ) * D.curvatureTensorNorm x := by
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let R := fun i j k l : I => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
    finrank_euclideanSpace_fin
  have htrace : (∑ p : I × I, R p.1 p.2 p.1 p.2) = D.scalarCurvature x := by
    simp only [Fintype.sum_prod_type]
    rfl
  have hdiag : (∑ p : I × I, (R p.1 p.2 p.1 p.2) ^ 2) ≤
      ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l) ^ 2 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, (R i j k l) ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ i))
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun p : I × I => R p.1 p.2 p.1 p.2)
  rw [htrace] at hcs
  have hcard : ((Finset.univ : Finset (I × I)).card : ℝ) = (n : ℝ) ^ 2 := by
    simp [I, hdim, pow_two]
  rw [hcard] at hcs
  have hsq := hcs.trans (mul_le_mul_of_nonneg_left hdiag (sq_nonneg (n : ℝ)))
  have hnorm : (D.curvatureTensorNorm x) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l) ^ 2 := by
    change (Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l) ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
  have hnormnonneg : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  have hboundnonneg : 0 ≤ (n : ℝ) * D.curvatureTensorNorm x := by positivity
  nlinarith only [hsq, hnorm, hboundnonneg, sq_abs (D.scalarCurvature x)]

theorem scalarCurvature_le_curvatureTensorNorm_sharp
    (D : LeviCivitaData g) (x : M) :
    D.scalarCurvature x ≤ (n : ℝ) * D.curvatureTensorNorm x :=
  (le_abs_self _).trans (D.abs_scalarCurvature_le_curvatureTensorNorm_sharp x)

set_option maxHeartbeats 800000 in

theorem curvatureTensorNorm_le_scalarCurvature_sharp
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hoperator : D.NonnegativeCurvatureOperator x) :
    D.curvatureTensorNorm x ≤ D.scalarCurvature x := by
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let R := fun i j k l : I => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hsym := hD.2.2.2.1
  have hlast : ∀ i j k l, R i j k l = -R i j l k :=
    fun i j k l => (hsym x (b i) (b j) (b k) (b l)).1
  have hpair : ∀ i j k l, R i j k l = R k l i j :=
    fun i j k l => (hsym x (b i) (b j) (b k) (b l)).2.1
  have hfirst : ∀ i j k l, R i j k l = -R j i k l := by
    intro i j k l
    rw [hpair i j k l, hlast k l i j, hpair k l j i]
  have hquad (U : I → I → ℝ) :
      0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * U i j * U k l := by
    have h := hoperator (fun i j => (U i j - U j i) / 2) (by
      unfold IsSkewCoefficient
      intros
      ring)
    have heq := Poincare.RicciFlow.Harnack.hamiltonBlock_antisymmetrize R
      (fun _ _ _ => 0) (fun _ _ => 0) U (fun _ => 0)
      hfirst hlast (by intros; simp)
    simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add] at heq
    rw [← heq]
    simpa only [curvatureOperatorQuadratic, R, b, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hpairquad (v : I × I → ℝ) :
      0 ≤ ∑ p, ∑ q, R p.1 p.2 q.1 q.2 * v p * v q := by
    simpa only [Fintype.sum_prod_type] using hquad (fun i j => v (i, j))
  have htrace : (∑ p : I × I, R p.1 p.2 p.1 p.2) = D.scalarCurvature x := by
    simp only [Fintype.sum_prod_type]
    rfl
  have hdiag (p : I × I) : 0 ≤ R p.1 p.2 p.1 p.2 := by
    have h := hpairquad (Pi.single p 1)
    simpa only [Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  have hscalar : 0 ≤ D.scalarCurvature x :=
    htrace ▸ Finset.sum_nonneg (fun p _ => hdiag p)
  have hsq : (∑ p : I × I, ∑ q : I × I, (R p.1 p.2 q.1 q.2) ^ 2) ≤
      (D.scalarCurvature x) ^ 2 := by
    calc
      _ ≤ ∑ p : I × I, ∑ q : I × I,
          R p.1 p.2 p.1 p.2 * R q.1 q.2 q.1 q.2 :=
        Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ =>
          Poincare.LinearAlgebra.entry_sq_le_diagonal_mul
            (fun p q : I × I => R p.1 p.2 q.1 q.2)
            (fun p q => hpair p.1 p.2 q.1 q.2) hpairquad p q))
      _ = (D.scalarCurvature x) ^ 2 := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
        rw [htrace, pow_two]
  apply (Real.sqrt_le_iff).2
  refine ⟨hscalar, ?_⟩
  simpa only [Fintype.sum_prod_type] using hsq

end PoincareConjecture.LeviCivitaData
