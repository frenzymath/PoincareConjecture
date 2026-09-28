import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleIntegration
import PoincareConjecture.Proofs.M03.Existence.SpectralSmallTimeNative














set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture



theorem m64AnnulusPoint_vertical_hasDerivAt (x t : ℝ) :
    HasDerivAt (annulusPoint x) (EuclideanSpace.single (1 : Fin 2) 1) t := by
  have heq : annulusPoint x = fun s =>
      annulusPoint x 0 + s • EuclideanSpace.single (1 : Fin 2) 1 := by
    funext s
    ext i
    fin_cases i <;> simp [annulusPoint]
  rw [heq]
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id t).smul_const (EuclideanSpace.single (1 : Fin 2) 1)).const_add
      (annulusPoint x 0)



theorem m64Annulus_vertical_trace_sq_le
    {f : LoopPlane → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (f (annulusPoint x s) - f (annulusPoint x 0)) ^ 2 ≤
      s * ∫ t in Icc (0 : ℝ) 1,
        (fderiv ℝ f (annulusPoint x t) (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2 := by
  let d : ℝ → ℝ := fun t =>
    fderiv ℝ f (annulusPoint x t) (EuclideanSpace.single (1 : Fin 2) 1)
  have hd : Continuous d := ((hf.continuous_fderiv (by simp)).comp
    (show Continuous (annulusPoint x) by unfold annulusPoint; fun_prop)).clm_apply continuous_const
  have hder (t : ℝ) : HasDerivAt (fun y => f (annulusPoint x y)) (d t) t :=
    (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (m64AnnulusPoint_vertical_hasDerivAt x t)
  have hFTC : f (annulusPoint x s) - f (annulusPoint x 0) = ∫ t in (0 : ℝ)..s, d t := by
    simpa only [Function.comp_apply] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
        (hd.intervalIntegrable 0 s)).symm
  rw [hFTC]
  apply (SpectralHeatNative.integral_sq_le_time_mul_integral_sq hs.1
    (hd.intervalIntegrable 0 s) ((hd.pow 2).intervalIntegrable 0 s)).trans
  apply mul_le_mul_of_nonneg_left _ hs.1
  rw [intervalIntegral.integral_of_le hs.1]
  exact setIntegral_mono_set ((hd.pow 2).integrableOn_Icc)
    (Eventually.of_forall fun t => sq_nonneg (d t))
    (Eventually.of_forall fun t ht => ⟨ht.1.le, ht.2.trans hs.2⟩)



theorem m64Annulus_lower_trace_l2_estimate
    {f : LoopPlane → ℝ} (hf : ContDiff ℝ 1 f) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ x in Icc (0 : ℝ) curvePeriod,
      (f (annulusPoint x s) - f (annulusPoint x 0)) ^ 2) ≤
      s * ∫ p in interior m64AnnulusDomain,
        (fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2 := by
  let D : LoopPlane → ℝ := fun p =>
    (fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2
  have hD : Continuous D :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
  have hproduct : Continuous (fun q : ℝ × ℝ => D (annulusPoint q.1 q.2)) := by
    apply hD.comp
    unfold annulusPoint
    fun_prop
  have hInt : Integrable (fun q : ℝ × ℝ => D (annulusPoint q.1 q.2))
      ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hproduct.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hleft : Continuous (fun x => (f (annulusPoint x s) - f (annulusPoint x 0)) ^ 2) := by
    apply Continuous.pow
    apply Continuous.sub <;> apply hf.continuous.comp <;> unfold annulusPoint <;> fun_prop
  calc
    _ ≤ ∫ x in Icc (0 : ℝ) curvePeriod, s * ∫ t in Icc (0 : ℝ) 1, D (annulusPoint x t) :=
      integral_mono hleft.integrableOn_Icc (hInt.integral_prod_left.const_mul s)
        (fun x => m64Annulus_vertical_trace_sq_le hf x hs)
    _ = s * ∫ x in Icc (0 : ℝ) curvePeriod, ∫ t in Icc (0 : ℝ) 1, D (annulusPoint x t) :=
      integral_const_mul _ _
    _ = _ := by rw [← m64AnnulusInteriorIntegral_eq_iterated D hD]

end PoincareConjecture
