import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTraceEstimate

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

theorem m64Annulus_lower_trace_interpolation
    {f : LoopPlane → ℝ} (hf : ContDiff ℝ 1 f) {delta : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) :
    (∫ x in Icc (0 : ℝ) curvePeriod, f (annulusPoint x 0) ^ 2) ≤
      (2 / delta) * (∫ p in interior m64AnnulusDomain, f p ^ 2) +
      2 * delta * (∫ p in interior m64AnnulusDomain,
        (fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2) := by
  let E : ℝ := ∫ p in interior m64AnnulusDomain,
    (fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2
  let T : ℝ := ∫ x in Icc (0 : ℝ) curvePeriod, f (annulusPoint x 0) ^ 2
  let J : ℝ → ℝ := fun s => ∫ x in Icc (0 : ℝ) curvePeriod,
    f (annulusPoint x s) ^ 2
  let U : ℝ := ∫ p in interior m64AnnulusDomain, f p ^ 2
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hprod : Continuous (fun q : ℝ × ℝ => f (annulusPoint q.1 q.2) ^ 2) := by
    apply Continuous.pow
    apply hf.continuous.comp
    unfold annulusPoint
    fun_prop
  have hInt (b : ℝ) : Integrable (fun q : ℝ × ℝ => f (annulusPoint q.1 q.2) ^ 2)
      ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod
        (volume.restrict (Icc (0 : ℝ) b))) := by
    rw [Measure.prod_restrict]
    exact hprod.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hJ (b : ℝ) : IntegrableOn J (Icc (0 : ℝ) b) volume :=
    (hInt b).integral_prod_right
  have hslice (s : ℝ) (hs : s ∈ Icc (0 : ℝ) delta) : T ≤ 2 * J s + 2 * delta * E := by
    have hc (t : ℝ) : Continuous (fun x => f (annulusPoint x t)) := by
      apply hf.continuous.comp
      unfold annulusPoint
      fun_prop
    have hdiff : IntegrableOn
        (fun x => (f (annulusPoint x s) - f (annulusPoint x 0)) ^ 2)
        (Icc (0 : ℝ) curvePeriod) volume := ((hc s).sub (hc 0)).pow 2 |>.integrableOn_Icc
    have hc2 (t : ℝ) : IntegrableOn (fun x => f (annulusPoint x t) ^ 2)
        (Icc (0 : ℝ) curvePeriod) volume := by
      have hct : Continuous (fun x => f (annulusPoint x t) ^ 2) := (hc t).pow 2
      exact hct.integrableOn_Icc
    have hbase : T ≤ 2 * J s + 2 * ∫ x in Icc (0 : ℝ) curvePeriod,
        (f (annulusPoint x s) - f (annulusPoint x 0)) ^ 2 := by
      calc
        T ≤ ∫ x in Icc (0 : ℝ) curvePeriod,
            (2 * f (annulusPoint x s) ^ 2 +
              2 * (f (annulusPoint x s) - f (annulusPoint x 0)) ^ 2) := by
          apply integral_mono (hc2 0) (((hc2 s).const_mul 2).add (hdiff.const_mul 2))
          intro x
          change f (annulusPoint x 0) ^ 2 ≤ 2 * f (annulusPoint x s) ^ 2 +
            2 * (f (annulusPoint x s) - f (annulusPoint x 0)) ^ 2
          nlinarith [sq_nonneg (2 * f (annulusPoint x s) - f (annulusPoint x 0))]
        _ = _ := by
          rw [integral_add ((hc2 s).const_mul 2)
            (hdiff.const_mul 2), integral_const_mul, integral_const_mul]
    have hcollar := m64Annulus_lower_trace_l2_estimate hf ⟨hs.1, hs.2.trans hd1⟩
    have hscale : s * E ≤ delta * E := mul_le_mul_of_nonneg_right hs.2 hE
    change _ ≤ s * E at hcollar
    linarith
  have hJU : (∫ s in Icc (0 : ℝ) delta, J s) ≤ U := by
    calc
      _ = ∫ x in Icc (0 : ℝ) curvePeriod,
          ∫ s in Icc (0 : ℝ) delta, f (annulusPoint x s) ^ 2 :=
        (integral_integral_swap (hInt delta)).symm
      _ ≤ ∫ x in Icc (0 : ℝ) curvePeriod,
          ∫ s in Icc (0 : ℝ) 1, f (annulusPoint x s) ^ 2 := by
        apply integral_mono (hInt delta).integral_prod_left (hInt 1).integral_prod_left
        intro x
        have hc : Continuous (fun s => f (annulusPoint x s) ^ 2) := by
          apply Continuous.pow
          apply hf.continuous.comp
          unfold annulusPoint
          fun_prop
        exact setIntegral_mono_set hc.integrableOn_Icc
          (Eventually.of_forall fun s => sq_nonneg _) (Eventually.of_forall fun s hs =>
            ⟨hs.1, hs.2.trans hd1⟩)
      _ = U := (m64AnnulusInteriorIntegral_eq_iterated (fun p => f p ^ 2)
        (hf.continuous.pow 2)).symm
  have havg : delta * T ≤ 2 * (∫ s in Icc (0 : ℝ) delta, J s) +
      2 * delta ^ 2 * E := by
    have hfinite : volume (Icc (0 : ℝ) delta) ≠ ⊤ := isCompact_Icc.measure_ne_top
    have hc : IntegrableOn (fun _ : ℝ => 2 * delta * E) (Icc (0 : ℝ) delta) volume :=
      integrableOn_const hfinite
    have hi := setIntegral_mono_on (integrableOn_const hfinite :
        IntegrableOn (fun _ : ℝ => T) (Icc (0 : ℝ) delta) volume)
      (((hJ delta).const_mul 2).add hc) measurableSet_Icc hslice
    simp only [Pi.add_apply, integral_add ((hJ delta).const_mul 2) hc,
      integral_const_mul, setIntegral_const, smul_eq_mul,
      Real.volume_real_Icc_of_le hd.le, sub_zero] at hi
    nlinarith
  change T ≤ (2 / delta) * U + 2 * delta * E
  have hbound : T * delta ≤ 2 * U + 2 * delta ^ 2 * E := by nlinarith
  calc
    T = (T * delta) / delta := by field_simp
    _ ≤ (2 * U + 2 * delta ^ 2 * E) / delta := div_le_div_of_nonneg_right hbound hd.le
    _ = _ := by field_simp

end PoincareConjecture
