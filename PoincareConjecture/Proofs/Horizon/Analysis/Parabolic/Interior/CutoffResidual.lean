import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.FrozenEstimate
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CutoffDerivatives
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Cutoffs
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CoefficientMatrix







noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Set
open scoped ContDiff RealInnerProductSpace BigOperators Topology

namespace Poincare.Parabolic.Interior

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem matrixLap_sub (A : Matrix ι ι ℝ)
    (D E : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F) :
    Kernel.matrixLap A (D - E) = Kernel.matrixLap A D - Kernel.matrixLap A E := by
  simp [Kernel.matrixLap, smul_sub, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
theorem matrixLap_smul (A : Matrix ι ι ℝ) (c : ℝ)
    (D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F) :
    Kernel.matrixLap A (c • D) = c • Kernel.matrixLap A D := by
  simp only [Kernel.matrixLap, _root_.smul_apply, Finset.smul_sum]
  congr 1
  funext i
  congr 1
  funext j
  exact smul_comm _ _ _

theorem norm_matrixLap_le_of_entry_bound (A : Matrix ι ι ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hA : ∀ i j, ‖A i j‖ ≤ L)
    (D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F) :
    ‖Kernel.matrixLap A D‖ ≤ (Fintype.card ι : ℝ) ^ 2 * L * ‖D‖ := by
  calc
    _ ≤ ∑ i : ι, ∑ j : ι, ‖A i j • D (EuclideanSpace.basisFun ι ℝ i)
        (EuclideanSpace.basisFun ι ℝ j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, L * ‖D‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      apply mul_le_mul (hA i j) _ (norm_nonneg _) hL
      simpa using ContinuousLinearMap.le_opNorm₂ D
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

theorem matrixHeatResidual_smul
    (A : Matrix ι ι ℝ) {χ : EuclideanSpace ℝ ι × ℝ → ℝ}
    {f : EuclideanSpace ℝ ι × ℝ → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (p : EuclideanSpace ℝ ι × ℝ) :
    matrixHeatResidual A (fun q => χ q • f q) p =
      χ p • matrixHeatResidual A f p + timeDerivative χ p • f p -
        Kernel.matrixLap A (spatialDerivative (spatialDerivative (fun q => χ q • f q)) p -
          χ p • spatialDerivative (spatialDerivative f) p) := by
  rw [matrixLap_sub, matrixLap_smul]
  simp only [matrixHeatResidual, timeDerivative_smul hχ hf, smul_sub]
  abel

theorem norm_matrixHeatResidual_smul_le
    (A : Matrix ι ι ℝ) {L : ℝ} (hL : 0 ≤ L) (hA : ∀ i j, ‖A i j‖ ≤ L)
    {χ : EuclideanSpace ℝ ι × ℝ → ℝ} {f : EuclideanSpace ℝ ι × ℝ → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (p : EuclideanSpace ℝ ι × ℝ) :
    ‖matrixHeatResidual A (fun q => χ q • f q) p‖ ≤
      ‖χ p‖ * ‖matrixHeatResidual A f p‖ + ‖timeDerivative χ p‖ * ‖f p‖ +
        (Fintype.card ι : ℝ) ^ 2 * L *
          (2 * ‖spatialDerivative χ p‖ * ‖spatialDerivative f p‖ +
            ‖spatialDerivative (spatialDerivative χ) p‖ * ‖f p‖) := by
  rw [matrixHeatResidual_smul A hχ hf]
  refine (norm_sub_le _ _).trans ?_
  have hcomm := norm_hessian_smul_sub_le
    (χ := fun y => χ (y, p.2)) (f := fun y => f (y, p.2))
    (hχ.comp (contDiff_id.prodMk contDiff_const))
    (hf.comp (contDiff_id.prodMk contDiff_const)) p.1
  have hsmooth : ContDiff ℝ ∞ (fun q => χ q • f q) := hχ.smul hf
  rw [fderiv_fderiv_spatialSlice hsmooth, fderiv_fderiv_spatialSlice hf,
    fderiv_spatialSlice hχ, fderiv_spatialSlice hf, fderiv_fderiv_spatialSlice hχ] at hcomm
  calc
    _ ≤ (‖χ p • matrixHeatResidual A f p‖ + ‖timeDerivative χ p • f p‖) +
        (Fintype.card ι : ℝ) ^ 2 * L *
          ‖spatialDerivative (spatialDerivative (fun q => χ q • f q)) p -
            χ p • spatialDerivative (spatialDerivative f) p‖ := by
      exact add_le_add (norm_add_le _ _) (norm_matrixLap_le_of_entry_bound A hL hA _)
    _ ≤ _ := by simp only [norm_smul]; gcongr

omit [DecidableEq ι] in
theorem spatialDerivative_of_notMem_tsupport {f : EuclideanSpace ℝ ι × ℝ → F}
    {p : EuclideanSpace ℝ ι × ℝ} (hp : p ∉ tsupport f) : spatialDerivative f p = 0 := by
  simp [spatialDerivative, fderiv_of_notMem_tsupport ℝ hp]

omit [DecidableEq ι] in
theorem tsupport_spatialDerivative_subset (f : EuclideanSpace ℝ ι × ℝ → F) :
    tsupport (spatialDerivative f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro p hp
  by_contra h
  exact hp (spatialDerivative_of_notMem_tsupport h)

theorem matrixHeatResidual_of_notMem_tsupport (A : Matrix ι ι ℝ)
    {f : EuclideanSpace ℝ ι × ℝ → F} {p : EuclideanSpace ℝ ι × ℝ}
    (hp : p ∉ tsupport f) : matrixHeatResidual A f p = 0 := by
  have hd : p ∉ tsupport (spatialDerivative f) :=
    fun h => hp (tsupport_spatialDerivative_subset f h)
  simp [matrixHeatResidual, timeDerivative, fderiv_of_notMem_tsupport ℝ hp,
    spatialDerivative_of_notMem_tsupport hd, Kernel.matrixLap]

omit [DecidableEq ι] in


theorem spatial_cutoff_commutator_eq_zero
    {χ : EuclideanSpace ℝ ι × ℝ → ℝ} {f : EuclideanSpace ℝ ι × ℝ → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (p : EuclideanSpace ℝ ι × ℝ)
    (hc : (fun y => χ (y, p.2)) =ᶠ[nhds p.1] fun _ => χ p) :
    spatialDerivative (spatialDerivative (fun q => χ q • f q)) p -
      χ p • spatialDerivative (spatialDerivative f) p = 0 := by
  have h₁ : spatialDerivative χ p = 0 := by
    rw [← fderiv_spatialSlice hχ, hc.fderiv_eq]
    simp
  have h₂ : spatialDerivative (spatialDerivative χ) p = 0 := by
    rw [← fderiv_fderiv_spatialSlice hχ, hc.fderiv.fderiv_eq]
    simp
  have h := norm_hessian_smul_sub_le
    (χ := fun y => χ (y, p.2)) (f := fun y => f (y, p.2))
    (hχ.comp (contDiff_id.prodMk contDiff_const))
    (hf.comp (contDiff_id.prodMk contDiff_const)) p.1
  have hsmooth : ContDiff ℝ ∞ (fun q => χ q • f q) := hχ.smul hf
  rw [fderiv_fderiv_spatialSlice hsmooth, fderiv_fderiv_spatialSlice hf,
    fderiv_spatialSlice hχ, fderiv_spatialSlice hf, fderiv_fderiv_spatialSlice hχ] at h
  simpa [h₁, h₂] using h



theorem norm_matrixHeatResidual_smul_le_centered
    (A : Matrix ι ι ℝ) {L K B G c₁ c₂ Q ρ : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hQ : 0 ≤ Q) (hρ : 0 < ρ)
    (hA : ∀ i j, ‖A i j‖ ≤ L)
    {χ : EuclideanSpace ℝ ι × ℝ → ℝ} {f : EuclideanSpace ℝ ι × ℝ → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ ι) (p : EuclideanSpace ℝ ι × ℝ)
    (hχbound : ‖χ p‖ ≤ 1)
    (hχ₁ : ‖spatialDerivative χ p‖ ≤ c₁)
    (hχ₂ : ‖spatialDerivative (spatialDerivative χ) p‖ ≤ c₂)
    (hnear : ‖p.1 - x‖ < ρ →
      (fun y => χ (y, p.2)) =ᶠ[nhds p.1] fun _ => χ p)
    (hb : p ∈ tsupport χ → ‖f p‖ ≤ B)
    (hg : p ∈ tsupport χ → ‖spatialDerivative f p‖ ≤ G)
    (hr : p ∈ tsupport χ → ‖matrixHeatResidual A f p‖ ≤ K * ‖p.1 - x‖ ^ (1 / 2 : ℝ))
    (hdt : p ∈ tsupport χ → ‖timeDerivative χ p‖ * ‖f p‖ ≤ Q) :
    ‖matrixHeatResidual A (fun q => χ q • f q) p‖ ≤
      (K + (Fintype.card ι : ℝ) ^ 2 * L * (2 * c₁ * G + c₂ * B) /
        ρ ^ (1 / 2 : ℝ)) * ‖p.1 - x‖ ^ (1 / 2 : ℝ) + Q := by
  by_cases hp : p ∈ tsupport χ
  · have hmain : ‖χ p‖ * ‖matrixHeatResidual A f p‖ ≤ K * ‖p.1 - x‖ ^ (1 / 2 : ℝ) := by
      calc
        _ ≤ 1 * (K * ‖p.1 - x‖ ^ (1 / 2 : ℝ)) := by gcongr; exact hr hp
        _ = _ := one_mul _
    have hcomm : ‖Kernel.matrixLap A
        (spatialDerivative (spatialDerivative (fun q => χ q • f q)) p -
          χ p • spatialDerivative (spatialDerivative f) p)‖ ≤
        ((Fintype.card ι : ℝ) ^ 2 * L * (2 * c₁ * G + c₂ * B) /
          ρ ^ (1 / 2 : ℝ)) * ‖p.1 - x‖ ^ (1 / 2 : ℝ) := by
      by_cases hn : ‖p.1 - x‖ < ρ
      · rw [spatial_cutoff_commutator_eq_zero hχ hf p (hnear hn)]
        simp only [Kernel.matrixLap, _root_.zero_apply, smul_zero,
          Finset.sum_const_zero, norm_zero]
        positivity
      · have hh := norm_hessian_smul_sub_le
          (χ := fun y => χ (y, p.2)) (f := fun y => f (y, p.2))
          (hχ.comp (contDiff_id.prodMk contDiff_const))
          (hf.comp (contDiff_id.prodMk contDiff_const)) p.1
        have hsmooth : ContDiff ℝ ∞ (fun q => χ q • f q) := hχ.smul hf
        rw [fderiv_fderiv_spatialSlice hsmooth, fderiv_fderiv_spatialSlice hf,
          fderiv_spatialSlice hχ, fderiv_spatialSlice hf, fderiv_fderiv_spatialSlice hχ] at hh
        have hbnd : ‖Kernel.matrixLap A
            (spatialDerivative (spatialDerivative (fun q => χ q • f q)) p -
              χ p • spatialDerivative (spatialDerivative f) p)‖ ≤
            (Fintype.card ι : ℝ) ^ 2 * L * (2 * c₁ * G + c₂ * B) := by
          refine (norm_matrixLap_le_of_entry_bound A hL hA _).trans ?_
          refine mul_le_mul_of_nonneg_left hh (by positivity) |>.trans ?_
          gcongr
          · exact hg hp
          · exact hb hp
        refine hbnd.trans ?_
        have hpow : ρ ^ (1 / 2 : ℝ) ≤ ‖p.1 - x‖ ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hρ.le (le_of_not_gt hn) (by norm_num)
        have hpos : 0 < ρ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
        calc
          _ = ((Fintype.card ι : ℝ) ^ 2 * L * (2 * c₁ * G + c₂ * B) /
              ρ ^ (1 / 2 : ℝ)) * ρ ^ (1 / 2 : ℝ) := (div_mul_cancel₀ _ hpos.ne').symm
          _ ≤ _ := by gcongr
    rw [matrixHeatResidual_smul A hχ hf]
    refine (norm_sub_le _ _).trans ?_
    have htri := norm_add_le (χ p • matrixHeatResidual A f p) (timeDerivative χ p • f p)
    simp only [norm_smul] at htri
    nlinarith [hdt hp]
  · rw [matrixHeatResidual_of_notMem_tsupport A
      (fun h => hp (tsupport_smul_subset_left χ f h))]
    rw [norm_zero]
    positivity



theorem norm_matrixHeatResidual_frozen_le
    {a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι × ℝ → F} {H M : ℝ} (hH : 0 ≤ H)
    (x y : EuclideanSpace ℝ ι) (s : ℝ)
    (ha : ‖a y - a x‖ ≤ H * ‖y - x‖ ^ (1 / 2 : ℝ))
    (hD : ‖spatialDerivative (spatialDerivative f) (y, s)‖ ≤ M)
    (hpde : timeDerivative f (y, s) =
      Kernel.matrixLap (coefficientMatrix (a y)) (spatialDerivative (spatialDerivative f) (y, s))) :
    ‖matrixHeatResidual (coefficientMatrix (a x)) f (y, s)‖ ≤
      ((Fintype.card ι : ℝ) ^ 2 * H * M) * ‖y - x‖ ^ (1 / 2 : ℝ) := by
  have hid (A B : Matrix ι ι ℝ)
      (D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F) :
      Kernel.matrixLap A D - Kernel.matrixLap B D = Kernel.matrixLap (A - B) D := by
    simp [Kernel.matrixLap, sub_smul, Finset.sum_sub_distrib]
  rw [matrixHeatResidual, hpde, hid]
  exact norm_matrixLap_coefficientMatrix_sub_le hH ha hD

end Poincare.Parabolic.Interior
