import PoincareConjecture.Proofs.M47.BlowupControlsCapAxialNormalizedJets
import PoincareConjecture.Proofs.M47.BlowupControlsCapAxialNorm
import PoincareConjecture.Proofs.M47.BlowupControlsCapAxialArithmetic










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates



theorem cap_native_axial_normalized_energy_le
    {gamma beta lambda bound : ℝ} (hgamma : 0 ≤ gamma)
    (hbeta : 0 < beta) (hupper : beta ≤ 301 / 300)
    (hlower : 1 - 4 * gamma ≤ beta) (hlambda : 0 ≤ lambda)
    (hscale : beta * lambda ^ 2 = 1)
    (hcenter : (beta - 1) ^ 2 ≤ (16 / 5 : ℝ) ^ 2 * bound)
    (c : ℝ) (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : RoundCylinderTensorSmoothOn gamma (fun z v w => B z v w))
    (m : ℕ) (horder : (m : ℝ) * gamma ≤ 1 / 6)
    (z : RoundCylinderSpace)
    (hz : (neckAxialSpaceMap lambda c z).2 ∈ Ioo (-gamma⁻¹) gamma⁻¹)
    (hpoint : roundCylinderJetErrorSquared 0 (fun z v w => B z v w) m
      (neckAxialSpaceMap lambda c z) ≤ bound) :
    roundCylinderJetErrorSquared 0
        (fun z v w => beta * neckAxialTensorPullback lambda c
          (fun z v w => B z v w) z v w) m z ≤ 36 * bound := by
  let p : V := (chartAt E2 z.1 z.1, z.2)
  let T (j : ℕ) := roundCylinderIteratedDerivative 0 (chartAt E2 z.1)
    (fun z v w => beta * neckAxialTensorPullback lambda c
      (fun z v w => B z v w) z v w) j p
  let D (j : ℕ) := roundCylinderIteratedDerivative 0 (chartAt E2 z.1)
    (fun z v w => B z v w) j (neckAxialCoordinate lambda c p)
  let W (j : ℕ) (a : Fin (2 + j) → Fin 3) :=
    beta * (∏ i, neckAxialWeight lambda (a i)) * D j a
  let f (j : ℕ) := roundCylinderTensorNormSquared 0 (chartAt E2 z.1)
    (neckAxialCoordinate lambda c p) (D j)
  let E := roundCylinderJetErrorSquared 0 (fun z v w => B z v w) m
    (neckAxialSpaceMap lambda c z)
  have hp : neckAxialCoordinate lambda c p ∈
      (chartAt E2 z.1).target ×ˢ Ioo (-gamma⁻¹) gamma⁻¹ :=
    ⟨(chartAt E2 z.1).map_source (mem_chart_source E2 z.1), hz⟩
  have hf0 (j : ℕ) : 0 ≤ f j :=
    M35.roundCylinderTensorNormSquared_nonneg zero_lt_one z.1
      (neckAxialSpaceMap lambda c z).2 _
  have hweight (j : ℕ) :
      roundCylinderTensorNormSquared 0 (chartAt E2 z.1) p (W j) ≤
        beta ^ 2 * (max 1 lambda) ^ (2 * (2 + j)) * f j :=
    cap_native_axial_weight_norm_le hlambda zero_lt_one beta z.1 z.2 (D j)
  have hzero : roundCylinderTensorNormSquared 0 (chartAt E2 z.1) p (T 0) ≤
      5 * (301 / 300 : ℝ) ^ 2 * f 0 + (5 / 2 : ℝ) * (beta - 1) ^ 2 := by
    have htri := cylinder_tensor_norm_weighted_le zero_lt_one z.1 z.2 (T 0) (W 0)
      (by norm_num : (0 : ℝ) < 4)
    have hdiff : (fun a => T 0 a - W 0 a) = fun a : Fin 2 → Fin 3 =>
        (beta - 1) * (roundCylinderGram 0 (chartAt E2 z.1) p (a 0) (a 1) -
          neckAxialConstantArray 1 a) := by
      funext a
      have h := cap_native_axial_normalized_zero beta lambda c 0 hscale B z.1 p a
      change T 0 a = beta * neckAxialTensorArray lambda c
        (roundCylinderIteratedDerivative 0 (chartAt E2 z.1) (fun z v w => B z v w) 0) p a + _ at h
      rw [h]
      dsimp only [W, D, neckAxialTensorArray]
      ring
    rw [hdiff, cap_native_sphere_error_norm_sq] at htri
    have hn := (hweight 0).trans (mul_le_mul_of_nonneg_right
      (cap_axial_normalization_zero_factor hbeta.le hupper hscale) (hf0 0))
    norm_num only at htri
    linarith only [htri, hn]
  have hpositive (j : ℕ) (hj : j + 1 ≤ m) :
      roundCylinderTensorNormSquared 0 (chartAt E2 z.1) p (T (j + 1)) ≤
        3 * f (j + 1) := by
    have heq : T (j + 1) = W (j + 1) := by
      funext a
      have h := cap_native_axial_normalized_succ beta lambda c zero_lt_one B z.1
        ((chartAt E2 z.1).open_target.prod isOpen_Ioo) (hB z.1) j p hp a
      exact h.trans (by dsimp only [W, D, neckAxialTensorArray]; ring)
    rw [heq]
    have hcast : ((j + 1 : ℕ) : ℝ) * gamma ≤ 1 / 6 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hgamma).trans horder
    have hfactor := cap_axial_normalization_order_factor hbeta hupper hlower hlambda
      hscale (j + 1) hcast
    have hfactor' : beta ^ 2 * (max 1 lambda) ^ (2 * (2 + (j + 1))) ≤ 3 := by
      simpa only [Nat.add_comm] using hfactor
    exact (hweight (j + 1)).trans
      (mul_le_mul_of_nonneg_right hfactor' (hf0 (j + 1)))
  have hbound (j : ℕ) (hj : j ≤ m) :
      roundCylinderTensorNormSquared 0 (chartAt E2 z.1) p (T j) ≤ 3 * f j +
        (if j = 0 then (5 * (301 / 300 : ℝ) ^ 2 - 3) * f 0 +
          (5 / 2 : ℝ) * (beta - 1) ^ 2 else 0) := by
    cases j with
    | zero => simp only [if_true]; linarith only [hzero]
    | succ j => simpa only [Nat.succ_ne_zero, if_false, add_zero] using hpositive j hj
  have hsum := Finset.sum_le_sum (s := Finset.range (m + 1))
    (fun j hj => hbound j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  have hfull : roundCylinderJetErrorSquared 0
      (fun z v w => beta * neckAxialTensorPullback lambda c
        (fun z v w => B z v w) z v w) m z ≤
        5 * (301 / 300 : ℝ) ^ 2 * f 0 + (5 / 2 : ℝ) * (beta - 1) ^ 2 + 3 * (E - f 0) := by
    apply hsum.trans_eq
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.succ_pos, if_true]
    change 3 * E + ((5 * (301 / 300 : ℝ) ^ 2 - 3) * f 0 +
      (5 / 2 : ℝ) * (beta - 1) ^ 2) = _
    ring
  have hE0 : f 0 ≤ E :=
    M35.roundCylinder_derivative_norm_le_jet zero_lt_one (fun z v w => B z v w)
      (neckAxialSpaceMap lambda c z) (Nat.zero_le m)
  exact hfull.trans (cap_axial_normalization_uniform_energy (hf0 0) hE0 hpoint hcenter)

end PoincareConjecture.M47
