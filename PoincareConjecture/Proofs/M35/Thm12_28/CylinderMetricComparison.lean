import PoincareConjecture.Proofs.M35.Thm12_28.NeckMetricJets
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

private theorem bilinear_basis_expansion
    (B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) :
    B v v = ∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
      B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  have hv : ∑ i : Fin 3, v i • EuclideanSpace.basisFun (Fin 3) ℝ i = v := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  calc
    B v v = B (∑ i : Fin 3, v i • EuclideanSpace.basisFun (Fin 3) ℝ i)
      (∑ j : Fin 3, v j • EuclideanSpace.basisFun (Fin 3) ℝ j) := by rw [hv]
    _ = _ := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
        Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem abs_bilinear_le_of_components
    (B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ i j : Fin 3,
      |B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ K)
    (v : EuclideanSpace ℝ (Fin 3)) : |B v v| ≤ 3 * K * ‖v‖ ^ 2 := by
  have hCS : (∑ i : Fin 3, |v i|) ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat, sq_abs,
      EuclideanSpace.real_norm_sq_eq] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 3 => |v i|))
  calc
    |B v v| = |∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
      B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)| :=
        congrArg abs (bilinear_basis_expansion B v)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |v i * v j *
      B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, K * |v i| * |v j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hB i j)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)
    _ = K * (∑ i : Fin 3, |v i|) ^ 2 := by
      simp only [sq, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ ≤ K * (3 * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hCS hK
    _ = 3 * K * ‖v‖ ^ 2 := by ring

theorem cylinderEuclideanCoefficients_lower {u : ℝ} (hu : u ≤ 0)
    (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 ≤ cylinderEuclideanCoefficients u (cylinderCoordinateEquiv.symm (0, s)) v v := by
  have hsplit : ‖v‖ ^ 2 = ‖(cylinderCoordinateEquiv v).1‖ ^ 2 +
      (cylinderCoordinateEquiv v).2 ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two,
      cylinderCoordinateEquiv_fst, cylinderCoordinateEquiv_snd]
    rfl
  rw [cylinderEuclideanCoefficients_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [norm_zero, real_inner_self_eq_norm_sq]
  norm_num
  have hscale : 0 ≤ (2 * (1 - u) - 1) * ‖(cylinderCoordinateEquiv v).1‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [hsplit]

end PoincareConjecture.M35

namespace PoincareConjecture.StandardCylinderPatch

theorem euclidean_pullback_lower {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hesmall : epsilon ≤ 1 / 24) (hu : u ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q)
        (M35.cylinderCoordinateEquiv.symm (0, s)) v v := by
  let p := M35.cylinderCoordinateEquiv.symm (0, s)
  let B := g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q) p
  let C := M35.cylinderEuclideanCoefficients u p
  have hp : M35.cylinderCoordinateEquiv p = (0, s) :=
    M35.cylinderCoordinateEquiv.apply_symm_apply (0, s)
  have hdom : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    simpa only [hp] using hs
  have huone : u < 1 := hu.2.trans_lt (by norm_num)
  have hB (i j : Fin 3) :
      |(B - C) (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ 4 * epsilon := by
    have hb := hclose.component_abs_lt he hu.1 huone (z := (q, s)) hs (Nat.zero_le _) ![i, j]
    dsimp only at hb
    rw [M35.sphere_chart_center] at hb
    norm_num [roundCylinderIteratedDerivative] at hb
    have hC := M35.cylinderEuclideanMetric_basis u huone q p i j
    change C (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) = _ at hC
    change |B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) -
      C (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ _
    rw [hC, N.euclideanChart_coefficient g q hdom, hp]
    exact hb.le
  have herr := M35.abs_bilinear_le_of_components (B - C) (by positivity) hB v
  change |B v v - C v v| ≤ 3 * (4 * epsilon) * ‖v‖ ^ 2 at herr
  have hmodel := M35.cylinderEuclideanCoefficients_lower hu.2 s v
  have hsmall : 3 * (4 * epsilon) * ‖v‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B v v
  have hlo := (abs_le.mp (herr.trans hsmall)).1
  change ‖v‖ ^ 2 ≤ C v v at hmodel
  linarith

end PoincareConjecture.StandardCylinderPatch
