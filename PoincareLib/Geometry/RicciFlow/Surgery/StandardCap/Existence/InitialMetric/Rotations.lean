import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Metric

/-!
# Invariance under the literal standard rotations

Definition 12.1 and Lemma 12.2, printed pp. 293-295, require invariance
under the specified SO(3) action, including its actual manifold derivative.
The matrix action is an ambient linear isometry; its derivative is the
same linear map, so the checked bilinear-form identity gives the required
metric invariance. No alternative action is substituted.
-/

set_option autoImplicit false

open Matrix
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- The literal matrix rotation preserves the ambient inner product
(Definition 12.1 and Lemma 12.2, pp. 293-295). -/
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

/-- The frozen standard rotation as an actual linear isometry
(Definition 12.1, p. 293). -/
noncomputable def capRotationIsometry (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    StandardCapSpace →ₗᵢ[ℝ] StandardCapSpace :=
  (Matrix.toLpLin 2 2 A.1).isometryOfInner (standardRotation_inner A)

/-- The manifold derivative of a standard rotation is its constant
linear map (Definition 12.1, p. 293). -/
theorem standardRotation_mfderiv (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : StandardCapSpace) :
    mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x =
      (capRotationIsometry A).toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  exact (capRotationIsometry A).toContinuousLinearMap.fderiv

/-- Invariance of the constructed cap metric under the contract's exact
SO(3) action and actual tangent derivative (Definition 12.1 and
Lemma 12.2, pp. 293-295). -/
theorem capRiemannianMetric_rotation_invariant (a : ℝ) (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : StandardCapSpace) (u v : TangentSpace (𝓡 3) x) :
    (capRiemannianMetric a ha hapi).inner (standardRotation A x)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
        (capRiemannianMetric a ha hapi).inner x u v := by
  rw [standardRotation_mfderiv]
  exact capMetricInner_linearIsometry a (capRotationIsometry A) x u v

end PoincareMT.M34
