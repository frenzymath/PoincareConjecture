import PoincareConjecture.Proofs.M60.Mathlib.HolomorphicFrame
import PoincareConjecture.Proofs.M60.Mathlib.HolomorphicFrameCutoff










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M60

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]



theorem cauchyRiemannDerivative_rescale {P : ℂ → W} (hP : Differentiable ℝ P)
    (z₀ : ℂ) (r : ℝ) (z : ℂ) :
    cauchyRiemannDerivative (fun w => P (r • (w - z₀))) z =
      r • cauchyRiemannDerivative P (r • (z - z₀)) := by
  have hS : HasFDerivAt (fun w : ℂ => r • (w - z₀))
      (r • ContinuousLinearMap.id ℝ ℂ) z := by
    convert! (r • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt.sub_const (r • z₀) using 1
    ext w
    simp only [smul_sub, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply]
  have hD := (hP (r • (z - z₀))).hasFDerivAt.comp z hS
  change HasFDerivAt (fun w => P (r • (w - z₀))) _ z at hD
  simp only [cauchyRiemannDerivative, hD.fderiv, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul]
  module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [CompleteSpace V]





theorem exists_local_c1_invertible_frame
    {A : ℂ → V →L[ℂ] V} {O : Set ℂ} (hO : IsOpen O)
    (hA : ContDiffOn ℝ 1 A O) {z₀ : ℂ} (hz₀ : z₀ ∈ O) :
    ∃ (s : ℝ) (P : ℂ → V →L[ℂ] V), 0 < s ∧ ball z₀ s ⊆ O ∧
      ContDiff ℝ 1 P ∧ (∀ z, IsUnit (P z)) ∧
      ∀ z ∈ ball z₀ s, cauchyRiemannDerivative P z = (A z).comp (P z) := by
  obtain ⟨d, B, hd, hB, hBc, hdO, hBA⟩ :=
    exists_compactlySupported_c1_extension hO hA hz₀
  obtain ⟨L, hL, hLb, hDLb⟩ := exists_c1_uniform_bound hB hBc
  let chi : ContDiffBump (0 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hchi : ContDiff ℝ 1 (chi : ℂ → ℝ) := chi.contDiff
  obtain ⟨D, hD, _, hDchi⟩ := exists_c1_uniform_bound hchi chi.hasCompactSupport
  obtain ⟨epsilon, hepsilon, hsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 4)
    (2 * cauchyKernelNorm * (D + 1) * L)
  let r : ℝ := min 1 epsilon
  have hr : 0 < r := lt_min zero_lt_one hepsilon
  have hr1 : r ≤ 1 := min_le_left _ _
  let a : ℝ := r * (D + 1) * L
  have ha : 0 ≤ a := by positivity
  have hCa : 2 * cauchyKernelNorm * a ≤ 1 / 4 := by
    calc
      _ = (2 * cauchyKernelNorm * (D + 1) * L) * r := by dsimp [a]; ring
      _ ≤ (2 * cauchyKernelNorm * (D + 1) * L) * epsilon := by
        apply mul_le_mul_of_nonneg_left (min_le_right _ _)
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          cauchyKernelNorm_nonneg) (by linarith)) hL
      _ ≤ 1 / 4 := hsmall.le
  let C := rescaledFrameCoefficient chi B z₀ r
  have hC : ContDiff ℝ 1 C := contDiff_rescaledFrameCoefficient hchi hB z₀ r
  have hCs : tsupport C ⊆ closedBall (0 : ℂ) 1 := by
    apply Subset.trans (tsupport_smul_subset_left (fun z => r * chi z)
      (fun z => B (z₀ + r • z)))
    apply tsupport_mul_subset_right.trans
    exact chi.tsupport_eq.subset
  have hCc : HasCompactSupport C :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _) hCs
  have hb (z : ℂ) : ‖C z‖ ≤ a ∧ ‖fderiv ℝ C z‖ ≤ a :=
    rescaledFrameCoefficient_bounds hchi hB hD hL hr.le hr1
      (fun _ => by rw [Real.norm_of_nonneg chi.nonneg]; exact chi.le_one)
      hDchi hLb hDLb z₀ z
  obtain ⟨Q, hQ, hQunit, hQeq⟩ := exists_c1_invertible_frame_of_smallCoefficient
    hC hCc hCs ha hCa (fun z => (hb z).1) (fun z => (hb z).2)
  let P : ℂ → V →L[ℂ] V := fun z => Q (r⁻¹ • (z - z₀))
  let s : ℝ := min d (r / 2)
  have hs : 0 < s := lt_min hd (half_pos hr)
  have hsd : s ≤ d := min_le_left _ _
  have hP : ContDiff ℝ 1 P := by
    apply hQ.comp
    exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
  refine ⟨s, P, hs, (ball_subset_ball hsd).trans hdO,
    hP,
    fun z => hQunit _, ?_⟩
  intro z hz
  let w : ℂ := r⁻¹ • (z - z₀)
  have hw : ‖w‖ < 1 / 2 := by
    have hz' : ‖z - z₀‖ < r / 2 :=
      (mem_ball_iff_norm.mp hz).trans_le (min_le_right _ _)
    change ‖r⁻¹ • (z - z₀)‖ < 1 / 2
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    calc
      _ < r⁻¹ * (r / 2) := mul_lt_mul_of_pos_left hz' (inv_pos.mpr hr)
      _ = 1 / 2 := by field_simp
  have hwr : z₀ + r • w = z := by
    change z₀ + r • (r⁻¹ • (z - z₀)) = z
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hchione : chi w = 1 := chi.one_of_mem_closedBall
    (by simpa only [mem_closedBall, dist_zero_right] using hw.le)
  have hCw : C w = r • A z := by
    change (r * chi w) • B (z₀ + r • w) = r • A z
    rw [hchione, mul_one, hwr, hBA ((ball_subset_ball hsd) hz)]
  change cauchyRiemannDerivative (fun y => Q (r⁻¹ • (y - z₀))) z = (A z).comp (Q w)
  rw [cauchyRiemannDerivative_rescale (hQ.differentiable (by simp))]
  change r⁻¹ • cauchyRiemannDerivative Q w = _
  rw [hQeq w (mem_ball_zero_iff.mpr (hw.trans (by norm_num))), hCw,
    ContinuousLinearMap.smul_comp, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

end PoincareConjecture.M60
