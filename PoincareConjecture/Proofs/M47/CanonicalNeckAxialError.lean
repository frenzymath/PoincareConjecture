import PoincareConjecture.Proofs.M47.CanonicalNeckAxialNorm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates



theorem roundCylinderJetErrorSquared_neckAxialTensorPullback_le
    {lambda u theta epsilon : ℝ} (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hu : u ≤ 0) (htheta : 0 < theta) (c : ℝ)
    (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : RoundCylinderTensorSmoothOn epsilon (fun z v w => B z v w))
    (m : ℕ) (z : RoundCylinderSpace)
    (hz : (neckAxialSpaceMap lambda c z).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    roundCylinderJetErrorSquared u
        (neckAxialTensorPullback lambda c (fun z v w => B z v w)) m z ≤
      (1 + theta) * roundCylinderJetErrorSquared u (fun z v w => B z v w) m
        (neckAxialSpaceMap lambda c z) +
      (1 + theta⁻¹) * (lambda ^ 2 - 1) ^ 2 := by
  let p : V := (chartAt E₂ z.1 z.1, z.2)
  let T (j : ℕ) := roundCylinderIteratedDerivative u (chartAt E₂ z.1)
    (neckAxialTensorPullback lambda c (fun z v w => B z v w)) j p
  let D (j : ℕ) := roundCylinderIteratedDerivative u (chartAt E₂ z.1)
    (fun z v w => B z v w) j (neckAxialCoordinate lambda c p)
  let W (j : ℕ) (a : Fin (2 + j) → Fin 3) :=
    (∏ i, neckAxialWeight lambda (a i)) * D j a
  have hp : neckAxialCoordinate lambda c p ∈
      (chartAt E₂ z.1).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨(chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1), hz⟩
  have hbound (j : ℕ) :
      roundCylinderTensorNormSquared u (chartAt E₂ z.1) p (T j) ≤
        (1 + theta) * roundCylinderTensorNormSquared u (chartAt E₂ z.1)
          (neckAxialCoordinate lambda c p) (D j) +
        (if j = 0 then (1 + theta⁻¹) * (lambda ^ 2 - 1) ^ 2 else 0) := by
    have htri := cylinder_tensor_norm_weighted_le (hu.trans_lt zero_lt_one)
      z.1 z.2 (T j) (W j) htheta
    have hnorm : roundCylinderTensorNormSquared u (chartAt E₂ z.1) p (W j) ≤
        roundCylinderTensorNormSquared u (chartAt E₂ z.1)
          (neckAxialCoordinate lambda c p) (D j) :=
      roundCylinderTensorNormSquared_neckAxialWeight_le hlambda hu z.1 z.2 (D j)
    cases j with
    | zero =>
      have hdiff : (fun a => T 0 a - W 0 a) =
          neckAxialConstantArray (lambda ^ 2 - 1) (r := 2) := by
        funext a
        have h := roundCylinderIteratedDerivative_neckAxialTensorPullback_zero
          lambda c u B z.1 p a
        change T 0 a = W 0 a +
          (lambda ^ 2 - 1) * (if a 0 = 2 ∧ a 1 = 2 then (1 : ℝ) else 0) at h
        rw [h]
        simp only [neckAxialConstantArray, Fin.forall_fin_two]
        ring
      rw [hdiff, roundCylinderTensorNormSquared_neckAxialConstantArray
        (hu.trans_lt zero_lt_one).ne] at htri
      exact htri.trans (add_le_add
        (mul_le_mul_of_nonneg_left hnorm (by positivity)) le_rfl)
    | succ j =>
      have hdiff : (fun a => T (j + 1) a - W (j + 1) a) = fun _ => (0 : ℝ) := by
        funext a
        have h := roundCylinderIteratedDerivative_neckAxialTensorPullback_succ lambda c
          (hu.trans_lt zero_lt_one) B z.1 ((chartAt E₂ z.1).open_target.prod isOpen_Ioo)
          (hB z.1) j p hp a
        change T (j + 1) a = W (j + 1) a at h
        exact sub_eq_zero.mpr h
      rw [hdiff] at htri
      have hzero : roundCylinderTensorNormSquared u (chartAt E₂ z.1) p
          (fun _ : Fin (2 + (j + 1)) → Fin 3 => (0 : ℝ)) = 0 := by
        simp [roundCylinderTensorNormSquared]
      change roundCylinderTensorNormSquared u (chartAt E₂ z.1) p (T (j + 1)) ≤
        (1 + theta) * roundCylinderTensorNormSquared u (chartAt E₂ z.1) p (W (j + 1)) +
          (1 + theta⁻¹) * roundCylinderTensorNormSquared u (chartAt E₂ z.1) p
            (fun _ : Fin (2 + (j + 1)) → Fin 3 => (0 : ℝ)) at htri
      rw [hzero, mul_zero, add_zero] at htri
      simp only [Nat.succ_ne_zero, if_false, add_zero]
      exact htri.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have hsum := Finset.sum_le_sum (s := Finset.range (m + 1)) (fun j _ => hbound j)
  change (∑ j ∈ Finset.range (m + 1),
      roundCylinderTensorNormSquared u (chartAt E₂ z.1) p (T j)) ≤
    (1 + theta) * (∑ j ∈ Finset.range (m + 1),
      roundCylinderTensorNormSquared u (chartAt E₂ z.1)
        (neckAxialCoordinate lambda c p) (D j)) +
      (1 + theta⁻¹) * (lambda ^ 2 - 1) ^ 2
  apply hsum.trans_eq
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

end PoincareConjecture.Proofs.M47
