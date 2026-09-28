import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerRescaledEstimate
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalInterface
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter ContinuousLinearMap
open scoped Topology Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

theorem suRoundFactor_smooth_pos :
    ContDiff ℝ ∞ suAlphaRoundFactor ∧ ∀ z, 0 < suAlphaRoundFactor z := by
  constructor
  · exact contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
      (fun _ => by positivity)
  · intro z
    unfold suAlphaRoundFactor
    positivity

theorem suRoundFactor_fderiv (z v : LoopPlane) :
    fderiv ℝ suAlphaRoundFactor z v =
      -64 * inner ℝ z v / (‖z‖ ^ 2 + 4) ^ 3 := by
  have hd := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (4 : ℝ)).pow 2
  have h := (((hasDerivAt_inv (by positivity : (‖z‖ ^ 2 + 4) ^ 2 ≠ 0)).comp_hasFDerivAt
    z hd).const_mul (16 : ℝ)).fderiv
  change fderiv ℝ (fun y : LoopPlane => 16 * ((‖y‖ ^ 2 + 4) ^ 2)⁻¹) z = _ at h
  change fderiv ℝ (fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2) z v = _
  simp only [div_eq_mul_inv]
  rw [h]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, Nat.cast_ofNat,
    nsmul_eq_mul, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem suRoundFactor_second (z v : LoopPlane) :
    fderiv ℝ (fun y => fderiv ℝ suAlphaRoundFactor y v) z v =
      -64 * ‖v‖ ^ 2 / (‖z‖ ^ 2 + 4) ^ 3 +
        384 * (inner ℝ z v) ^ 2 / (‖z‖ ^ 2 + 4) ^ 4 := by
  have hn : HasFDerivAt (fun y => -64 * inner ℝ y v) ((-64 : ℝ) • innerSL ℝ v) z := by
    convert! (innerSL ℝ v).hasFDerivAt.const_mul (-64) using 1
    ext y
    exact congrArg (fun a : ℝ => -64 * a) (real_inner_comm v y)
  have hd := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (4 : ℝ)).pow 3
  have h := (hn.mul ((hasDerivAt_inv
    (by positivity : (‖z‖ ^ 2 + 4) ^ 3 ≠ 0)).comp_hasFDerivAt z hd)).fderiv
  change fderiv ℝ (fun y : LoopPlane => -64 * inner ℝ y v * ((‖y‖ ^ 2 + 4) ^ 3)⁻¹) z = _ at h
  simp_rw [suRoundFactor_fderiv]
  simp only [div_eq_mul_inv]
  rw [h]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, Nat.cast_ofNat, nsmul_eq_mul, Nat.reduceSub,
    Function.comp_apply]
  field_simp
  ring

theorem suRoundFactor_laplacian (z : LoopPlane) :
    (∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ suAlphaRoundFactor y
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      -128 / (‖z‖ ^ 2 + 4) ^ 3 + 384 * ‖z‖ ^ 2 / (‖z‖ ^ 2 + 4) ^ 4 := by
  simp only [suRoundFactor_second, OrthonormalBasis.norm_eq_one, one_pow,
    EuclideanSpace.inner_basisFun_real, mul_one, Fin.sum_univ_two]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  ring

theorem suRoundFactor_rescaled_bounds (a : LoopPlane) {s R : ℝ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) (hR : R ≤ 1) :
    let l := fun z : LoopPlane => suAlphaRoundFactor (a + s • z)
    ∀ z ∈ Metric.closedBall 0 R, 1 / 4 ≤ l z ∧ l z ≤ 4 ∧
      (fderiv ℝ l z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ^ 2 +
        (fderiv ℝ l z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ^ 2 ≤ 256 ∧
      (∑ i : Fin 2, fderiv ℝ (fun w => fderiv ℝ l w
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) ≤ 64 := by
  intro l z hz
  let w := a + s • z
  let d : ℝ := ‖w‖ ^ 2 + 4
  have hzn : ‖z‖ ≤ 1 := (show ‖z‖ ≤ R by simpa using hz).trans hR
  have hwn : ‖w‖ ≤ 2 := by
    calc
      ‖w‖ ≤ ‖a‖ + ‖s • z‖ := norm_add_le _ _
      _ = ‖a‖ + s * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
      _ ≤ 2 := by nlinarith [norm_nonneg z]
  have hw2 : ‖w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg w]
  have hd4 : 4 ≤ d := by dsimp only [d]; nlinarith [sq_nonneg ‖w‖]
  have hd8 : d ≤ 8 := by dsimp only [d]; linarith
  have hd : 0 < d := by linarith
  have hd2 : 16 ≤ d ^ 2 := by nlinarith
  have hd2' : d ^ 2 ≤ 64 := by nlinarith
  have hl : l z = 16 / d ^ 2 := rfl
  have hfirst (i : Fin 2) : fderiv ℝ l z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      -64 * s * w i / d ^ 3 := by
    rw [suRescale_fderiv]
    simp only [smul_apply, smul_eq_mul, suRoundFactor_fderiv, EuclideanSpace.inner_basisFun_real]
    dsimp only [w, d]
    ring
  have hnorm : w 0 ^ 2 + w 1 ^ 2 = ‖w‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hl]
    apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith
  · rw [hl]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith
  · rw [hfirst 0, hfirst 1]
    have hden : 4096 ≤ d ^ 6 := by
      calc
        (4096 : ℝ) = 4 ^ 6 := by norm_num
        _ ≤ d ^ 6 := pow_le_pow_left₀ (by norm_num) hd4 6
    have hnum : 4096 * s ^ 2 * (w 0 ^ 2 + w 1 ^ 2) ≤ 16384 := by
      rw [hnorm]
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hs2 (sq_nonneg ‖w‖)]
    have heq : (-64 * s * w 0 / d ^ 3) ^ 2 + (-64 * s * w 1 / d ^ 3) ^ 2 =
        4096 * s ^ 2 * (w 0 ^ 2 + w 1 ^ 2) / d ^ 6 := by ring
    rw [heq]
    apply (div_le_iff₀ (pow_pos hd 6)).mpr
    nlinarith
  · have hsecond : (∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ l y
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        s ^ 2 * (-128 / d ^ 3 + 384 * ‖w‖ ^ 2 / d ^ 4) := by
      simp only [l, suRescale_second_fderiv, smul_eq_mul]
      rw [← Finset.mul_sum, suRoundFactor_laplacian]
    have hden : 256 ≤ d ^ 4 := by
      calc
        (256 : ℝ) = 4 ^ 4 := by norm_num
        _ ≤ d ^ 4 := pow_le_pow_left₀ (by norm_num) hd4 4
    have hpos : 0 ≤ 384 * ‖w‖ ^ 2 / d ^ 4 := by positivity
    have hupp : 384 * ‖w‖ ^ 2 / d ^ 4 ≤ 6 := by
      apply (div_le_iff₀ (pow_pos hd 4)).mpr
      nlinarith
    have hneg : -128 / d ^ 3 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    rw [hsecond]
    nlinarith [mul_le_mul_of_nonneg_left hneg (sq_nonneg s),
      mul_le_mul_of_nonneg_right hs2 hpos]

end PoincareConjecture.M60

end
