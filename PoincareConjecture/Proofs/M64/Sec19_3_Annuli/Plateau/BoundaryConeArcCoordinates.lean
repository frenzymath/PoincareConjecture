import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeReconstruction

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64BoundaryCone

open M65Interior

theorem semicircle_coordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {N : ℕ} (H : E → EuclideanSpace ℝ (Fin N))
    {L : NNReal} {K : ℝ} (hH : ContDiff ℝ 1 H) (hLip : LipschitzWith L H)
    (hHD : ∀ y, ‖fderiv ℝ H y‖ ≤ K) {V W : ℝ → E}
    (hV : AbsolutelyContinuousOnInterval V 0 Real.pi)
    (hW : MemLp W 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      V t - V s = ∫ theta in s..t, W theta) :
    let v := H ∘ V
    let d := fun theta => fderiv ℝ H (V theta) (W theta)
    AbsolutelyContinuousOnInterval v 0 Real.pi ∧
      MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
        v t - v s = ∫ theta in s..t, d theta) ∧
      (∫ theta in Icc (0 : ℝ) Real.pi, ‖d theta‖ ^ 2) ≤
        K ^ 2 * ∫ theta in Icc (0 : ℝ) Real.pi, ‖W theta‖ ^ 2 := by
  let d := fun theta => fderiv ℝ H (V theta) (W theta)
  have hVC : ContinuousOn V (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hV.continuousOn
  have hDb (theta : ℝ) : ‖d theta‖ ≤ K * ‖W theta‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hHD _) (norm_nonneg _))
  have hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) := by
    apply hW.of_le_mul _ (ae_of_all _ hDb)
    have hcoeff : AEStronglyMeasurable (fun theta => fderiv ℝ H (V theta))
        (volume.restrict (Icc (0 : ℝ) Real.pi)) :=
      ((hH.continuous_fderiv one_ne_zero).comp_continuousOn hVC).aestronglyMeasurable
        measurableSet_Icc
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hcoeff.prodMk hW.1)
  have hWI : IntervalIntegrable W volume 0 Real.pi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr
      (hW.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  refine ⟨ac_comp_lipschitz hV hLip.lipschitzOnWith (mapsTo_univ _ _), hd, ?_, ?_⟩
  · intro s hs t ht
    have hdIcc : IntegrableOn d (Icc (0 : ℝ) Real.pi) :=
      hd.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hdi : IntervalIntegrable d volume s t :=
      (hdIcc.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
    ext j
    let pr : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := EuclideanSpace.proj j
    have hj (theta : ℝ) : fderiv ℝ (pr ∘ H) (V theta) (W theta) = pr (d theta) := by
      rw [(pr.hasFDerivAt.comp (V theta)
        ((hH.differentiable one_ne_zero _).hasFDerivAt)).fderiv]
      rfl
    have hi := (ac_chain_integral Real.pi_pos hV
      (pr.lipschitz.comp hLip).lipschitzOnWith (mapsTo_univ _ _)
      (fun theta _ => pr.differentiableAt.comp _ (hH.differentiable one_ne_zero _))
      hWI hinc).2.2.2 s hs t ht
    change pr (H (V t)) - pr (H (V s)) = pr (∫ theta in s..t, d theta)
    rw [← pr.intervalIntegral_comp_comm hdi]
    simpa only [Function.comp_apply, hj] using hi
  · rw [← integral_const_mul]
    apply integral_mono_ae hd.norm.integrable_sq (hW.norm.integrable_sq.const_mul _)
    exact ae_of_all _ fun theta => by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hDb theta) 2

end PoincareConjecture.M64BoundaryCone
