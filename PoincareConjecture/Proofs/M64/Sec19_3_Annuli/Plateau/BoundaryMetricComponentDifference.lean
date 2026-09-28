import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryAutonomousDifference












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Poincare.Analysis.Sobolev

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => E × E

local instance m64ComponentDifference_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64ComponentDifference_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64ComponentDifference_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64ComponentDifference_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1000000 in





theorem m64WeightedMetric_component_difference
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (w : Fin 2 → ℝ) (u : LoopPlane → E) (V : Fin 2 → LoopPlane → E)
    (dx : Fin 2 → ℝ) (x : LoopPlane) {kappa mu C Lambda h xi : ℝ}
    (hk : 0 < kappa) (hmu : 0 < mu) (hC : 0 ≤ C)
    (hw : ∀ i, mu ≤ w i ∧ w i ≤ Lambda) (hh : h ≠ 0)
    (hG : ‖G (u (x + h • EuclideanSpace.single 0 1))‖ ≤ C)
    (hT : ‖T (u (x + h • EuclideanSpace.single 0 1))‖ ≤ C)
    (hpos : ∀ v : E, kappa * ‖v‖ ^ 2 ≤
      G (u (x + h • EuclideanSpace.single 0 1)) v v)
    (hGL : ‖G (u (x + h • EuclideanSpace.single 0 1)) - G (u x)‖ ≤
      C * ‖u (x + h • EuclideanSpace.single 0 1) - u x‖)
    (hTL : ‖T (u (x + h • EuclideanSpace.single 0 1)) - T (u x)‖ ≤
      C * ‖u (x + h • EuclideanSpace.single 0 1) - u x‖) :
    let F := fun (a : Fin n) (i : Fin 2) (p : LoopPlane) =>
      w i * G (u p) (V i p) (EuclideanSpace.single a 1)
    let b := fun (a : Fin n) (p : LoopPlane) =>
      -(∑ i : Fin 2, w i * T (u p) (EuclideanSpace.single a 1) (V i p) (V i p)) / 2
    let H := ‖(V 0 (x + h • EuclideanSpace.single 0 1),
      V 1 (x + h • EuclideanSpace.single 0 1))‖ ^ 2 + ‖(V 0 x, V 1 x)‖ ^ 2
    let nu := kappa * mu
    let K := 2 * Lambda * C
    nu / 4 * (∑ a : Fin n, ∑ i : Fin 2,
      (xi * diffQuot 0 h (fun p => V i p a) x) ^ 2) ≤
      (∑ a : Fin n, ∑ i : Fin 2, diffQuot 0 h (F a i) x *
        (xi ^ 2 * diffQuot 0 h (fun p => V i p a) x +
          2 * xi * dx i * diffQuot 0 h (fun p => u p a) x)) -
      (∑ a : Fin n, diffQuot 0 h (b a) x *
        (xi ^ 2 * diffQuot 0 h (fun p => u p a) x)) +
      (32 * K ^ 2 / nu + 6 * K) *
        ((H * xi ^ 2 + ∑ a : Fin n,
          H * (xi * diffQuot 0 h (fun p => u p a) x) ^ 2) +
          ∑ a : Fin n, ∑ i : Fin 2, (dx i * diffQuot 0 h (fun p => u p a) x) ^ 2) := by
  let y := x + h • EuclideanSpace.single (0 : Fin 2) 1
  let U := h⁻¹ • (u y - u x)
  let d := fun i : Fin 2 => h⁻¹ • (V i y - V i x)
  let L := h⁻¹ • (m64WeightedPairMetric w (G (u y)) (V 0 y, V 1 y) -
    m64WeightedPairMetric w (G (u x)) (V 0 x, V 1 x))
  let B := h⁻¹ • (m64WeightedQuadraticSource w (T (u y)) (V 0 y, V 1 y) -
    m64WeightedQuadraticSource w (T (u x)) (V 0 x, V 1 x))
  have hnorm : |h| * ‖U‖ = ‖u y - u x‖ := by
    rw [show ‖U‖ = |h⁻¹| * ‖u y - u x‖ by simp [U, norm_smul]]
    rw [← mul_assoc, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hh), one_mul]
  have hp := m64WeightedMetric_autonomous_difference_pointwise w (G (u x)) (G (u y))
    (T (u x)) (T (u y)) (V 0 y, V 1 y) (V 0 x, V 1 x)
    (dx 0 • U, dx 1 • U) U (xi := xi) hk hmu hC hw hG hT hpos hh
    (by rw [hnorm]; exact hGL) (by rw [hnorm]; exact hTL)
  have hLambda : 0 ≤ Lambda := hmu.le.trans ((hw 0).1.trans (hw 0).2)
  have hK : 0 ≤ 2 * Lambda * C := by positivity
  have hb := M60.suNaturalGrowth_column_pointwise L B d U dx
    (nu := kappa * mu / 2) (C := 32 * (2 * Lambda * C) ^ 2 / (kappa * mu) +
      6 * (2 * Lambda * C)) (W := 1)
    (H := ‖(V 0 y, V 1 y)‖ ^ 2 + ‖(V 0 x, V 1 x)‖ ^ 2)
    (by positivity) (by positivity) zero_le_one (by simpa only [one_mul, d, Prod.smul_mk,
      Prod.mk_sub_mk, L, B] using hp)
  have hd (i : Fin 2) (a : Fin n) : d i a = diffQuot 0 h (fun p => V i p a) x := by
    simp only [d, y, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, diffQuot, hh,
      if_false, div_eq_mul_inv, mul_comm]
  have hU (a : Fin n) : U a = diffQuot 0 h (fun p => u p a) x := by
    simp only [U, y, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, diffQuot, hh,
      if_false, div_eq_mul_inv, mul_comm]
  have hL (a : Fin n) (i : Fin 2) : L (M60.suColumnBasis a i) =
      diffQuot 0 h (fun p => w i * G (u p) (V i p) (EuclideanSpace.single a 1)) x := by
    fin_cases i <;> simp [L, y, M60.suColumnBasis, m64WeightedPairMetric_apply,
      diffQuot, hh, div_eq_mul_inv, mul_comm]
  have hB (a : Fin n) : B (EuclideanSpace.single a 1) =
      diffQuot 0 h (fun p => -(∑ i : Fin 2,
        w i * T (u p) (EuclideanSpace.single a 1) (V i p) (V i p)) / 2) x := by
    simp only [B, m64WeightedQuadraticSource, smul_apply, sub_apply, smul_eq_mul,
      m64WeightedPairMetricDerivative_apply, diffQuot, hh, if_false, Fin.sum_univ_two, y]
    ring
  simp only [hL, hB, hd, hU, one_mul] at hb
  convert hb using 1
  ring

end PoincareConjecture
