
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.TensorReaction
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.Reaction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators
open Poincare.Geometry.Curvature.Operator Poincare.HamiltonIvey

namespace PoincareConjecture.LeviCivitaData

private theorem tensorReaction_curvatureOperator_apply
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    tensorReaction (TensorFiber.operatorTensor (curvatureOperator R))
        ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j] =
      Poincare.Geometry.Curvature.Operator.curvatureReaction (curvatureMatrix R) i j := by
  rw [tensorReaction_operatorTensor, TensorFiber.operatorTensor_apply]
  have h := toMatrix_endomorphismReaction_eq_curvatureReaction
    (EuclideanSpace.basisFun (Fin 3) ℝ) (curvatureOperator R)
  have hmatrix : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (curvatureOperator R) =
      curvatureMatrix R := by
    rw [curvatureOperator, Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  rw [hmatrix] at h
  simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis] using
      congrFun (congrFun h i) j

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private instance reactionFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance



theorem tensorReaction_ricciComplementTensor_apply_orthonormalBasis [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) (i j : Fin 3),
      tensorReaction (D.ricciComplementTensor hD x) ![b i, b j] =
        Poincare.Geometry.Curvature.Operator.curvatureReaction
          (curvatureMatrix (fun i j k l =>
            D.curvatureTensor x (b i) (b j) (b k) (b l))) i j := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b i j
  rw [D.ricciComplementTensor_eq_transport_operatorTensor hD x b,
    tensorReaction_transport, TensorFiber.transport_apply]
  convert tensorReaction_curvatureOperator_apply
    (fun p q r s => D.curvatureTensor x (b p) (b q) (b r) (b s)) i j using 1
  congr 1
  ext k
  fin_cases k <;> simp [OrthonormalBasis.repr_self, EuclideanSpace.basisFun_apply]



theorem tensorReaction_ricciComplementTensor_eq_curvatureB [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) (i j : Fin 3),
      tensorReaction (D.ricciComplementTensor hD x) ![b i, b j] =
        2 * (D.curvatureB x (b (pairFirst i)) (b (pairSecond i))
            (b (pairFirst j)) (b (pairSecond j)) -
          D.curvatureB x (b (pairFirst i)) (b (pairSecond i))
            (b (pairSecond j)) (b (pairFirst j)) -
          D.curvatureB x (b (pairFirst i)) (b (pairSecond j))
            (b (pairSecond i)) (b (pairFirst j)) +
          D.curvatureB x (b (pairFirst i)) (b (pairFirst j))
            (b (pairSecond i)) (b (pairSecond j))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b i j
  rw [D.tensorReaction_ricciComplementTensor_apply_orthonormalBasis hD x b]
  exact (D.curvatureB_cyclic_reaction hD x b i j).symm

end PoincareConjecture.LeviCivitaData
