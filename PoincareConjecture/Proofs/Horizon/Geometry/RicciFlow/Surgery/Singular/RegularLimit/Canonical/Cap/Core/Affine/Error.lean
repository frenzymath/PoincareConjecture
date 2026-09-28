import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Jets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderAffine

noncomputable def errorPullback (c a s : ℝ) (B : RoundCylinderTwoTensor) : RoundCylinderTwoTensor :=
  fun z v w => EvolvingRoundCylinderMetric 0 z v w +
    c * (pullback a s B z v w - pullback a s (EvolvingRoundCylinderMetric 0) z v w)

theorem model_homogeneous (u : ℝ) (z : RoundCylinderSpace) (a b : ℝ)
    (v w : RoundCylinderTangent z) :
    EvolvingRoundCylinderMetric u z (a • v) (b • w) =
      a * b * EvolvingRoundCylinderMetric u z v w := by
  change EvolvingRoundCylinderMetric u z (a • v.1, a * v.2) (b • w.1, b * w.2) = _
  simp only [EvolvingRoundCylinderMetric,
    map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem derivative_const_mul (c u : ℝ) (q : UnitTwoSphere) {r : ℕ}
    (A : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (p : RoundCylinderCoordinates) (i : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (fun p i => c * A p i) p i =
      c * roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) A p i := by
  have hd : fderiv ℝ (fun p => c * A p (fun k => i k.succ)) p =
      c • fderiv ℝ (fun p => A p (fun k => i k.succ)) p := by
    change fderiv ℝ (c • fun p => A p (fun k => i k.succ)) p = _
    rw [fderiv_const_smul_field]
    rfl
  unfold roundCylinderTensorDerivative
  rw [hd]
  simp only [smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem iteratedDerivative_errorPullback (c a s : ℝ) (ha : a ≠ 0)
    (B : RoundCylinderTwoTensor)
    (hB : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (q : UnitTwoSphere) :
    ∀ k : ℕ, roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (errorPullback c a s B) k =
      fun p i => c * tensorPullback a s
        (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k) p i
  | 0 => by
    funext p i
    change roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (i 0) (i 1) +
        c * (roundCylinderTensorCoefficient (pullback a s B)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (i 0) (i 1) -
          roundCylinderTensorCoefficient (pullback a s (EvolvingRoundCylinderMetric 0))
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (i 0) (i 1)) -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (i 0) (i 1) = _
    rw [coefficient_pullback a s B hB,
      coefficient_pullback a s (EvolvingRoundCylinderMetric 0) (model_homogeneous 0)]
    simp only [tensorPullback, tensorWeight, Fin.prod_univ_succ, Fin.prod_univ_zero,
      mul_one, Fin.succ_zero_eq_one, roundCylinderIteratedDerivative, roundCylinderGram]
    ring
  | k + 1 => by
    change roundCylinderTensorDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (errorPullback c a s B) k) = _
    rw [iteratedDerivative_errorPullback c a s ha B hB q k]
    funext p i
    rw [derivative_const_mul,
      derivative_tensorPullback a s ha (by norm_num : (0 : ℝ) ≠ 1)]
    rfl

theorem errorPullback_jetError_le (c a s : ℝ) (ha : 0 < a) (haone : a ≤ 1)
    (B : RoundCylinderTwoTensor)
    (hB : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared 0 (errorPullback c a s B) order z ≤
      c ^ 2 * roundCylinderJetErrorSquared 0 B order (space a s z) := by
  unfold roundCylinderJetErrorSquared
  dsimp only [space]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [iteratedDerivative_errorPullback c a s ha.ne' B hB]
  rw [SingularRegularLimit.cylinderNorm_smul (by norm_num : (0 : ℝ) ≠ 1)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
  let q := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (q z.1, z.2)
  let A := roundCylinderIteratedDerivative 0 q B k (coordinates a s p)
  exact tensorNorm_contraction ha.le haone (by norm_num : (0 : ℝ) < 1) z.1 p A

end PoincareConjecture.RoundCylinderAffine
