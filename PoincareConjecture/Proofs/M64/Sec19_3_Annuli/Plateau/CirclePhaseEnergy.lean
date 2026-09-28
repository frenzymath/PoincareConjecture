import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTraceEstimate

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

theorem m64AnnulusPoint_horizontal_hasDerivAt (s x : ℝ) :
    HasDerivAt (fun y => annulusPoint y s) (EuclideanSpace.single (0 : Fin 2) 1) x := by
  have heq : (fun y => annulusPoint y s) = fun y =>
      annulusPoint 0 s + y • EuclideanSpace.single (0 : Fin 2) 1 := by
    funext y
    ext i
    fin_cases i <;> simp [annulusPoint]
  rw [heq]
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id x).smul_const (EuclideanSpace.single (0 : Fin 2) 1)).const_add
      (annulusPoint 0 s)

theorem m64Annulus_phase_slice_energy
    {L : LoopPlane → ℝ} (hL : ContDiff ℝ 1 L) {d : ℝ}
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d)
    (s : ℝ) :
    d ^ 2 ≤ curvePeriod * ∫ x in Icc (0 : ℝ) curvePeriod,
      (fderiv ℝ L (annulusPoint x s) (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2 := by
  let D : ℝ → ℝ := fun x =>
    fderiv ℝ L (annulusPoint x s) (EuclideanSpace.single (0 : Fin 2) 1)
  have hD : Continuous D := ((hL.continuous_fderiv (by simp)).comp
    (show Continuous (fun x => annulusPoint x s) by unfold annulusPoint; fun_prop)).clm_apply
      continuous_const
  have hder (x : ℝ) : HasDerivAt (fun y => L (annulusPoint y s)) (D x) x :=
    (hL.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x
      (m64AnnulusPoint_horizontal_hasDerivAt s x)
  have hFTC : d = ∫ x in (0 : ℝ)..curvePeriod, D x := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
      (hD.intervalIntegrable 0 curvePeriod)
    have hs := hshift 0 s
    simp only [zero_add] at hs
    rw [hs] at hh
    simpa only [add_sub_cancel_left] using hh.symm
  have hp : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  rw [hFTC]
  have hh := SpectralHeatNative.integral_sq_le_time_mul_integral_sq hp
    (hD.intervalIntegrable 0 curvePeriod) ((hD.pow 2).intervalIntegrable 0 curvePeriod)
  simpa only [intervalIntegral.integral_of_le hp, ← integral_Icc_eq_integral_Ioc] using hh

theorem m64Annulus_phase_energy
    {L : LoopPlane → ℝ} (hL : ContDiff ℝ 1 L) {d : ℝ}
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d) :
    d ^ 2 ≤ curvePeriod * ∫ p in interior m64AnnulusDomain,
      (fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2 := by
  let D : LoopPlane → ℝ := fun p =>
    (fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2
  have hD : Continuous D :=
    ((hL.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
  have hprod : Continuous (fun q : ℝ × ℝ => D (annulusPoint q.1 q.2)) := by
    apply hD.comp
    unfold annulusPoint
    fun_prop
  have hInt : Integrable (fun q : ℝ × ℝ => D (annulusPoint q.1 q.2))
      ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hprod.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc
    d ^ 2 = ∫ _s in Icc (0 : ℝ) 1, d ^ 2 := by simp
    _ ≤ ∫ s in Icc (0 : ℝ) 1,
        curvePeriod * ∫ x in Icc (0 : ℝ) curvePeriod, D (annulusPoint x s) := by
      apply integral_mono (show IntegrableOn (fun _ : ℝ => d ^ 2) (Icc (0 : ℝ) 1) volume
        from integrableOn_const isCompact_Icc.measure_ne_top)
        (hInt.integral_prod_right.const_mul curvePeriod)
      exact m64Annulus_phase_slice_energy hL hshift
    _ = curvePeriod * ∫ s in Icc (0 : ℝ) 1,
        ∫ x in Icc (0 : ℝ) curvePeriod, D (annulusPoint x s) := integral_const_mul _ _
    _ = curvePeriod * ∫ x in Icc (0 : ℝ) curvePeriod,
        ∫ s in Icc (0 : ℝ) 1, D (annulusPoint x s) := by
      exact congrArg (fun r : ℝ => curvePeriod * r) (integral_integral_swap hInt).symm
    _ = _ := by rw [← m64AnnulusInteriorIntegral_eq_iterated D hD]

end PoincareConjecture
