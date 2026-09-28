import PoincareConjecture.Proofs.M60.Mathlib.HolomorphicFrameEstimates
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M60

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]



theorem exists_compactlySupported_c1_extension
    {A : ℂ → W} {O : Set ℂ} (hO : IsOpen O) (hA : ContDiffOn ℝ 1 A O)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O) :
    ∃ (d : ℝ) (B : ℂ → W), 0 < d ∧ ContDiff ℝ 1 B ∧ HasCompactSupport B ∧
      ball z₀ d ⊆ O ∧ EqOn B A (ball z₀ d) := by
  obtain ⟨r, hr, hrO⟩ := nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hz₀)
  let chi : ContDiffBump z₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let B : ℂ → W := fun z => chi z • A z
  have hs : tsupport (chi : ℂ → ℝ) ⊆ O := by rw [chi.tsupport_eq]; exact hrO
  have hB : ContDiff ℝ 1 B := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport (chi : ℂ → ℝ)
    · exact chi.contDiff.contDiffAt.smul
        ((hA z (hs hz)).contDiffAt (hO.mem_nhds (hs hz)))
    · apply (contDiffAt_const (c := (0 : W))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
      simp [B, hw]
  refine ⟨r / 2, B, half_pos hr, hB, chi.hasCompactSupport.smul_right, ?_, ?_⟩
  · exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hrO
  · intro z hz
    change chi z • A z = A z
    rw [chi.one_of_mem_closedBall (ball_subset_closedBall hz), one_smul]



theorem exists_c1_uniform_bound {A : ℂ → W}
    (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ z, ‖A z‖ ≤ L) ∧ (∀ z, ‖fderiv ℝ A z‖ ≤ L) := by
  obtain ⟨L₀, hL₀⟩ := hA.continuous.bounded_above_of_compact_support hc
  obtain ⟨L₁, hL₁⟩ :=
    (hA.continuous_fderiv (by simp)).bounded_above_of_compact_support (hc.fderiv ℝ)
  exact ⟨max 0 (max L₀ L₁), le_max_left _ _,
    fun z => (hL₀ z).trans ((le_max_left _ _).trans (le_max_right _ _)),
    fun z => (hL₁ z).trans ((le_max_right _ _).trans (le_max_right _ _))⟩



theorem norm_fderiv_real_smul_le {f : ℂ → ℝ} {g : ℂ → W} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    ‖fderiv ℝ (fun w => f w • g w) z‖ ≤
      ‖f z‖ * ‖fderiv ℝ g z‖ + ‖fderiv ℝ f z‖ * ‖g z‖ := by
  rw [fderiv_fun_smul hf hg]
  exact (norm_add_le _ _).trans_eq
    (by rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply])



noncomputable def rescaledFrameCoefficient (chi : ℂ → ℝ) (A : ℂ → W)
    (z₀ : ℂ) (r : ℝ) : ℂ → W :=
  fun z => (r * chi z) • A (z₀ + r • z)



theorem contDiff_rescaledFrameCoefficient {chi : ℂ → ℝ} {A : ℂ → W}
    (hchi : ContDiff ℝ 1 chi) (hA : ContDiff ℝ 1 A) (z₀ : ℂ) (r : ℝ) :
    ContDiff ℝ 1 (rescaledFrameCoefficient chi A z₀ r) := by
  have hS : ContDiff ℝ 1 (fun z : ℂ => z₀ + r • z) :=
    contDiff_const.add (contDiff_id.const_smul r)
  exact (contDiff_const.mul hchi).smul (hA.comp hS)



theorem rescaledFrameCoefficient_bounds {chi : ℂ → ℝ} {A : ℂ → W}
    (hchi : ContDiff ℝ 1 chi) (hA : ContDiff ℝ 1 A)
    {D L r : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hchib : ∀ z, ‖chi z‖ ≤ 1) (hDchib : ∀ z, ‖fderiv ℝ chi z‖ ≤ D)
    (hAb : ∀ z, ‖A z‖ ≤ L) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ L) (z₀ z : ℂ) :
    ‖rescaledFrameCoefficient chi A z₀ r z‖ ≤ r * (D + 1) * L ∧
      ‖fderiv ℝ (rescaledFrameCoefficient chi A z₀ r) z‖ ≤ r * (D + 1) * L := by
  let S : ℂ → ℂ := fun w => z₀ + r • w
  have hS : HasFDerivAt S (r • ContinuousLinearMap.id ℝ ℂ) z := by
    simpa [S] using ((hasFDerivAt_id z).const_smul r).const_add z₀
  have hAc : DifferentiableAt ℝ (A ∘ S) z :=
    ((hA.differentiable (by simp)) (S z)).comp z hS.differentiableAt
  have hDAc : ‖fderiv ℝ (A ∘ S) z‖ ≤ L * r := by
    rw [((hA.differentiable (by simp)) (S z)).hasFDerivAt.comp z hS |>.fderiv]
    calc
      _ ≤ ‖fderiv ℝ A (S z)‖ * ‖r • ContinuousLinearMap.id ℝ ℂ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ L * r := by
        rw [norm_smul, Real.norm_of_nonneg hr, ContinuousLinearMap.norm_id, mul_one]
        exact mul_le_mul_of_nonneg_right (hDAb _) hr
  have hdc : HasFDerivAt (fun w => r * chi w) (r • fderiv ℝ chi z) z :=
    ((hchi.differentiable (by simp)) z).hasFDerivAt.const_mul r
  have hcb : ‖r * chi z‖ ≤ r := by
    rw [norm_mul, Real.norm_of_nonneg hr]
    exact mul_le_of_le_one_right hr (hchib z)
  have hDcb : ‖fderiv ℝ (fun w => r * chi w) z‖ ≤ r * D := by
    rw [hdc.fderiv, norm_smul, Real.norm_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (hDchib z) hr
  constructor
  · change ‖(r * chi z) • A (S z)‖ ≤ _
    rw [norm_smul]
    calc
      _ ≤ r * L := mul_le_mul hcb (hAb _) (norm_nonneg _) hr
      _ ≤ r * (D + 1) * L := by nlinarith [mul_nonneg hr hL, mul_nonneg hD (mul_nonneg hr hL)]
  · apply (norm_fderiv_real_smul_le hdc.differentiableAt hAc).trans
    calc
      _ ≤ r * (L * r) + (r * D) * L := by
        exact add_le_add (mul_le_mul hcb hDAc (norm_nonneg _) hr)
          (mul_le_mul hDcb (hAb _) (norm_nonneg _) (mul_nonneg hr hD))
      _ ≤ r * (D + 1) * L := by nlinarith [mul_nonneg hr hL]

end PoincareConjecture.M60
