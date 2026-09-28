import PoincareConjecture.Proofs.M09.CurvatureDerivativeSymmetry
import PoincareConjecture.Proofs.M09.CurvatureBianchi
import PoincareConjecture.Definitions.Ch06.LGeometry

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

theorem scalarCurvature_mvfderiv_of_bianchi (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M)
    (hB : ∀ a u v w z : TangentSpace (𝓡 n) p,
      D.covariantTensorDerivative D.riemannEvaluation p ![a, u, v, w, z] +
        D.covariantTensorDerivative D.riemannEvaluation p ![u, v, a, w, z] +
        D.covariantTensorDerivative D.riemannEvaluation p ![v, a, u, w, z] = 0)
    (X : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) D.scalarCurvature p X =
      2 * ∑ i, ricciDerivativePairing D p (g.orthonormalBasis p i) X
        (g.orthonormalBasis p i) := by
  let e := g.orthonormalBasis p
  let R := fun a u v w z ↦
    D.covariantTensorDerivative D.riemannEvaluation p ![a, u, v, w, z]
  have hsecond : (∑ i, ∑ j, R (e i) (e j) X (e i) (e j)) =
      -(∑ i, ∑ j, R (e i) X (e j) (e i) (e j)) := by
    calc
      _ = ∑ i, ∑ j, -R (e i) X (e j) (e i) (e j) :=
        Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦
          covariantRiemannDerivative_first_antisymm hM04 D p (e i) (e j) X (e i) (e j)))
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hthird : (∑ i, ∑ j, R (e j) X (e i) (e i) (e j)) =
      -(∑ i, ∑ j, R (e i) X (e j) (e i) (e j)) := by
    calc
      _ = ∑ i, ∑ j, R (e i) X (e j) (e j) (e i) := Finset.sum_comm
      _ = ∑ i, ∑ j, -R (e i) X (e j) (e i) (e j) :=
        Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦
          covariantRiemannDerivative_last_antisymm hM04 D p (e i) X (e j) (e j) (e i)))
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hb : (∑ i, ∑ j, (R X (e i) (e j) (e i) (e j) +
      R (e i) (e j) X (e i) (e j) + R (e j) X (e i) (e i) (e j))) = 0 :=
    Finset.sum_eq_zero (fun i _ ↦ Finset.sum_eq_zero (fun j _ ↦ hB X (e i) (e j) (e i) (e j)))
  simp only [Finset.sum_add_distrib] at hb
  rw [hsecond, hthird] at hb
  rw [scalarCurvature_mvfderiv_contraction hM04 D]
  simp only [ricciDerivativePairing, covariantRicci_eq_contraction hM04 D]
  change (∑ i, ∑ j, R X (e i) (e j) (e i) (e j)) =
    2 * ∑ i, ∑ j, R (e i) X (e j) (e i) (e j)
  linarith

theorem squareTime_scalarCurvature_mvfderiv_contracted_bianchi
    {J : Set ℝ} (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (X : TangentSpace (𝓡 n) p) :
    let D := F.connection (T - s ^ 2)
    mvfderiv (𝓡 n) D.scalarCurvature p X =
      2 * ∑ i, ricciDerivativePairing D p ((F.metric (T - s ^ 2)).orthonormalBasis p i)
        X ((F.metric (T - s ^ 2)).orthonormalBasis p i) :=
  scalarCurvature_mvfderiv_of_bianchi hM04 (F.connection (T - s ^ 2)) p
    (squareTime_curvature_second_bianchi F hM04 T b hb hwindow p s hs) X

end PoincareConjecture.Proofs.M09
