import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.Metric











set_option autoImplicit false

open Matrix
open scoped Manifold ContDiff

namespace PoincareConjecture.M34



theorem standardRotation_inner (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (u v : StandardCapSpace) :
    inner ℝ (standardRotation A u) (standardRotation A v) = inner ℝ u v := by
  have hA : A.1.transpose * A.1 = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.2).1
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (A.1 *ᵥ WithLp.ofLp v) ⬝ᵥ (A.1 *ᵥ WithLp.ofLp u) =
    WithLp.ofLp v ⬝ᵥ WithLp.ofLp u
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose A.1 (WithLp.ofLp v),
    Matrix.vecMul_vecMul, hA, Matrix.vecMul_one]



noncomputable def capRotationIsometry (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    StandardCapSpace →ₗᵢ[ℝ] StandardCapSpace :=
  (Matrix.toLpLin 2 2 A.1).isometryOfInner (standardRotation_inner A)



theorem standardRotation_mfderiv (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : StandardCapSpace) :
    mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x =
      (capRotationIsometry A).toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  exact (capRotationIsometry A).toContinuousLinearMap.fderiv




theorem capRiemannianMetric_rotation_invariant (a : ℝ) (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : StandardCapSpace) (u v : TangentSpace (𝓡 3) x) :
    (capRiemannianMetric a ha hapi).inner (standardRotation A x)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
        (capRiemannianMetric a ha hapi).inner x u v := by
  rw [standardRotation_mfderiv]
  exact capMetricInner_linearIsometry a (capRotationIsometry A) x u v

end PoincareConjecture.M34
