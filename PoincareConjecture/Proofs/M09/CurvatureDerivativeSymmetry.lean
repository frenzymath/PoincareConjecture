import PoincareConjecture.Proofs.M09.RicciDerivative

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

theorem curvatureTensor_first_antisymm (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (u v w z : TangentSpace (𝓡 n) p) :
    D.curvatureTensor p u v w z = -D.curvatureTensor p v u w z := by
  have hs := (hM04.tensor_calculus n M g D).2.2.2.1
  rw [(hs p u v w z).2.1, (hs p w z u v).1, (hs p w z v u).2.1]

theorem covariantRiemannDerivative_first_antisymm (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (a u v w z : TangentSpace (𝓡 n) p) :
    D.covariantTensorDerivative D.riemannEvaluation p ![a, u, v, w, z] =
      -D.covariantTensorDerivative D.riemannEvaluation p ![a, v, u, w, z] := by
  have hR := (hM04.tensor_calculus n M g D).1
  let P := frozenConnectionEndomorphism D p a
  have heq : (fun q ↦ frameCurvatureSlice D hR p u w q v z) =
      -(fun q ↦ frameCurvatureSlice D hR p v w q u z) := by
    funext q
    simp only [Pi.neg_apply, frameCurvatureSlice_apply]
    exact curvatureTensor_first_antisymm hM04 D q _ _ _ _
  have hd : mvfderiv (𝓡 n) (fun q ↦ frameCurvatureSlice D hR p u w q v z) p a =
      -mvfderiv (𝓡 n) (fun q ↦ frameCurvatureSlice D hR p v w q u z) p a := by
    rw [heq, mvfderiv_neg]
    rfl
  rw [frameCurvatureSlice_derivative, frameCurvatureSlice_derivative] at hd
  change _ + D.curvatureTensor p (P u) v w z + D.curvatureTensor p u (P v) w z +
      D.curvatureTensor p u v (P w) z + D.curvatureTensor p u v w (P z) =
      -(_ + D.curvatureTensor p (P v) u w z + D.curvatureTensor p v (P u) w z +
        D.curvatureTensor p v u (P w) z + D.curvatureTensor p v u w (P z)) at hd
  rw [curvatureTensor_first_antisymm hM04 D p (P v) u w z,
    curvatureTensor_first_antisymm hM04 D p v (P u) w z,
    curvatureTensor_first_antisymm hM04 D p v u (P w) z,
    curvatureTensor_first_antisymm hM04 D p v u w (P z)] at hd
  linarith

theorem covariantRiemannDerivative_last_antisymm (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (a u v w z : TangentSpace (𝓡 n) p) :
    D.covariantTensorDerivative D.riemannEvaluation p ![a, u, v, w, z] =
      -D.covariantTensorDerivative D.riemannEvaluation p ![a, u, v, z, w] := by
  have hR := (hM04.tensor_calculus n M g D).1
  have hs := (hM04.tensor_calculus n M g D).2.2.2.1
  let P := frozenConnectionEndomorphism D p a
  have heq : (fun q ↦ frameCurvatureSlice D hR p u w q v z) =
      -(fun q ↦ frameCurvatureSlice D hR p u z q v w) := by
    funext q
    simp only [Pi.neg_apply, frameCurvatureSlice_apply]
    exact (hs q _ _ _ _).1
  have hd : mvfderiv (𝓡 n) (fun q ↦ frameCurvatureSlice D hR p u w q v z) p a =
      -mvfderiv (𝓡 n) (fun q ↦ frameCurvatureSlice D hR p u z q v w) p a := by
    rw [heq, mvfderiv_neg]
    rfl
  rw [frameCurvatureSlice_derivative, frameCurvatureSlice_derivative] at hd
  change _ + D.curvatureTensor p (P u) v w z + D.curvatureTensor p u (P v) w z +
      D.curvatureTensor p u v (P w) z + D.curvatureTensor p u v w (P z) =
      -(_ + D.curvatureTensor p (P u) v z w + D.curvatureTensor p u (P v) z w +
        D.curvatureTensor p u v (P z) w + D.curvatureTensor p u v z (P w)) at hd
  rw [(hs p (P u) v z w).1, (hs p u (P v) z w).1,
    (hs p u v (P z) w).1, (hs p u v z (P w)).1] at hd
  linarith

end PoincareConjecture.Proofs.M09
