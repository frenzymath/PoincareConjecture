import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import PoincareConjecture.Proofs.M62.Lemma19_9_Length










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem hasDerivAt_regularizedTotal
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {ε t : ℝ}
    (hε : 0 < ε) (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (m62RegularizedTotalCurvature F c ε)
      (∫ x in (0 : ℝ)..curvePeriod,
        deriv (fun s => m62RegularizedCurvature F c ε s x * curveSpeed F c s x) t) t := by
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  let V := fun z : ℝ × ℝ => m62RegularizedCurvature F c ε z.2 z.1 * curveSpeed F c z.2 z.1
  have hV : ContDiffOn ℝ ∞ V (Set.Icc 0 curvePeriod ×ˢ Set.Ioo a b) :=
    ((regularized_smooth F c hε (curvatureSquared_contDiffOn F c hc)).mul
      (speed_joint_contDiffOn F c hc)).mono
        (Set.prod_mono (Set.subset_univ _) Set.Subset.rfl)
  apply (M08.hasDerivAt_variationIntegral hperiod isOpen_Ioo V hV ht).congr_deriv
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc 0 curvePeriod := by
    simpa only [Set.uIcc_of_le hperiod.le] using hx
  exact (M08.hasDerivAt_variationParameter isOpen_Ioo V hV hx' ht).deriv.symm

set_option maxHeartbeats 800000 in



theorem regularized_total_deriv_le [T2Space M]
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Set.Ioo a b) :
    deriv (m62RegularizedTotalCurvature F c ε) t ≤
      (m62C1 K0 K1 K2 + K2) * m62RegularizedTotalCurvature F c ε t +
        m62C1 K0 K1 K2 * m62Length F c t := by
  let h := m62RegularizedCurvature F c ε t
  let v := curveSpeed F c t
  let Lh := m62ArcSecondDerivative F c t h
  let A := m62C1 K0 K1 K2 + K2
  let B := m62C1 K0 K1 K2
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hh : ContDiff ℝ ∞ h :=
    (regularized_smooth F c hε (curvatureSquared_contDiffOn F c hc)).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hv : ContDiff ℝ ∞ v :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hvi := hv.inv (fun x => (speed_pos F c hc hclosed x).ne')
  have hfirst : ContDiff ℝ ∞ (m62ArcDerivative F c t h) :=
    hvi.mul (contDiff_infty_iff_deriv.mp hh).2
  have hsecond : ContDiff ℝ ∞ Lh :=
    hvi.mul (contDiff_infty_iff_deriv.mp hfirst).2
  let V := fun z : ℝ × ℝ => m62RegularizedCurvature F c ε z.2 z.1 * curveSpeed F c z.2 z.1
  have hV : ContDiffOn ℝ ∞ V (Set.univ ×ˢ Set.Ioo a b) :=
    (regularized_smooth F c hε (curvatureSquared_contDiffOn F c hc)).mul
      (speed_joint_contDiffOn F c hc)
  have hpartial := M08.variationParameterDeriv_contDiffOn
    (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set ℝ)) isOpen_Ioo V hV
  have hdensity : Continuous (fun x => deriv (fun s => V (x, s)) t) := by
    convert hpartial.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, ht⟩) using 1
    funext x
    exact (M08.hasDerivAt_variationParameter isOpen_Ioo V hV (Set.mem_univ x) ht).deriv
  have hLhi : IntervalIntegrable (fun x => Lh x * v x) MeasureTheory.volume 0 curvePeriod :=
    (hsecond.continuous.mul hv.continuous).intervalIntegrable 0 curvePeriod
  have hhi : IntervalIntegrable (fun x => h x * v x) MeasureTheory.volume 0 curvePeriod :=
    (hh.continuous.mul hv.continuous).intervalIntegrable 0 curvePeriod
  have hvi' := hv.continuous.intervalIntegrable (μ := MeasureTheory.volume) 0 curvePeriod
  calc
    _ = ∫ x in (0 : ℝ)..curvePeriod, deriv (fun s => V (x, s)) t :=
      (hasDerivAt_regularizedTotal F c hc hε ht).deriv
    _ ≤ ∫ x in (0 : ℝ)..curvePeriod, (Lh x + A * h x + B) * v x := by
      apply intervalIntegral.integral_mono hperiod (hdensity.intervalIntegrable _ _)
        ((((hsecond.continuous.add (hh.continuous.const_mul A)).add continuous_const).mul
          hv.continuous).intervalIntegrable _ _)
      intro x
      have hRt := regularized_hasDerivAt_time F c hε
        (hasDerivAt_curvatureSquared F c hc ht x)
      have hd := hRt.differentiableAt.hasDerivAt.mul (hasDerivAt_speed F c hc ht x)
      have hderiv : deriv (fun s => m62RegularizedCurvature F c ε s x *
          curveSpeed F c s x) t =
        deriv (fun s => m62RegularizedCurvature F c ε s x) t * curveSpeed F c t x +
          m62RegularizedCurvature F c ε t x *
            (-(m62TangentRicci F c t x + m62CurvatureSquared F c t x) *
              curveSpeed F c t x) := hd.deriv
      have hb := regularized_deriv_le F c hc h0 h1 h2 hBounds hε ht x
      have hunit := (unitTangent_norm F c hc hclosed x).le
      have hRic : -K2 ≤ m62TangentRicci F c t x :=
        (abs_le.mp (hBounds.ricci t hclosed (c x t)
          (spatialUnitTangent F c t x) (spatialUnitTangent F c t x) hunit hunit)).1
      have hRicmul := mul_le_mul_of_nonneg_left hRic (regularized_pos F c hε t x).le
      have hcubic : (m62Curvature F c t x) ^ 3 ≤ h x * m62CurvatureSquared F c t x := by
        calc
          _ = m62Curvature F c t x * (m62Curvature F c t x) ^ 2 := by ring
          _ ≤ h x * (m62Curvature F c t x) ^ 2 :=
            mul_le_mul_of_nonneg_right (curvature_le_regularized F c ε t x) (sq_nonneg _)
          _ = _ := by rw [curvature_sq F c t x]
      have hscalar : deriv (fun s => m62RegularizedCurvature F c ε s x) t -
          h x * (m62CurvatureSquared F c t x + m62TangentRicci F c t x) ≤
            Lh x + A * h x + B := by
        dsimp only [Lh, A, B, h] at *
        nlinarith only [hb, hcubic, hRicmul]
      change deriv (fun s => m62RegularizedCurvature F c ε s x * curveSpeed F c s x) t ≤ _
      rw [hderiv]
      convert! mul_le_mul_of_nonneg_right hscalar (speed_nonneg F c t x) using 1
      ring
    _ = (∫ x in (0 : ℝ)..curvePeriod, Lh x * v x) +
        A * (∫ x in (0 : ℝ)..curvePeriod, h x * v x) +
          B * (∫ x in (0 : ℝ)..curvePeriod, v x) := by
      simp_rw [add_mul, mul_assoc]
      rw [intervalIntegral.integral_add (hLhi.add (hhi.const_mul A)) (hvi'.const_mul B),
        intervalIntegral.integral_add hLhi (hhi.const_mul A),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [integral_regularized_arcSecond_eq_zero F c hc hε ht, zero_add]
      rfl

end PoincareConjecture.M62
