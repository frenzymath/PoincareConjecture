import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeWeakEquation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchWeakCRMultiplier
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchWeakCRRegularity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeTransform













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Complex
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture.M65Branch




theorem dbar_clm_comp {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : E →L[ℂ] G) {F : ℂ → E} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    dbar (fun w => L (F w)) z = L (dbar F z) := by
  have hd := (L.restrictScalars ℝ).hasFDerivAt.comp z hF.hasFDerivAt
  change HasFDerivAt (fun w => L (F w)) _ z at hd
  simp only [dbar, hd.fderiv, dbarLinear, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_add, map_smul]




theorem contDiff_inverse_operator {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Q : ℂ → E →L[ℂ] E} (hQ : ContDiff ℝ 1 Q)
    (hunit : ∀ z, IsUnit (Q z)) :
    ContDiff ℝ 1 (fun z => Ring.inverse (Q z)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨u, hu⟩ := hunit z
  have hi : ContDiffAt ℝ 1 Ring.inverse (Q z) := by
    simpa only [hu] using contDiffAt_ringInverse ℝ (n := 1) u
  exact hi.comp z hQ.contDiffAt





theorem dbar_inverse_operator_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {A Q : ℂ → E →L[ℂ] E} {z : ℂ}
    (hQ : ContDiff ℝ 1 Q) (hunit : ∀ w, IsUnit (Q w))
    (heq : dbar Q z = A z * Q z) (v : E) :
    dbar (fun w => Ring.inverse (Q w) v) z =
      -Ring.inverse (Q z) (A z v) := by
  let R (w : ℂ) := Ring.inverse (Q w)
  have hR := contDiff_inverse_operator hQ hunit
  have hRv : ContDiff ℝ 1 (fun w => R w v) :=
    ((ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ).contDiff.comp hR
  have hid : (fun w => Q w (R w v)) = fun _ : ℂ => v := by
    funext w
    change (Q w * Ring.inverse (Q w)) v = v
    rw [Ring.mul_inverse_cancel _ (hunit w)]
    rfl
  have hp := dbar_clm_apply (hQ.differentiable one_ne_zero z)
    (hRv.differentiable one_ne_zero z)
  rw [hid, heq] at hp
  have hz : dbar (fun _ : ℂ => v) z = 0 := by
    simp [dbar, dbarLinear, fderiv_const_apply]
  rw [hz] at hp
  change 0 = A z (Q z (R z v)) + Q z (dbar (fun w => R w v) z) at hp
  rw [congrFun hid z] at hp
  have hr := congrArg (R z) hp
  change R z 0 = R z (A z v + Q z (dbar (fun w => R w v) z)) at hr
  rw [map_zero, map_add] at hr
  have hcancel (x : E) : R z (Q z x) = x := by
    change (Ring.inverse (Q z) * Q z) x = x
    rw [Ring.inverse_mul_cancel _ (hunit z)]
    rfl
  rw [hcancel] at hr
  exact add_eq_zero_iff_eq_neg.mp (by simpa only [add_comm] using hr.symm)

private theorem operator_apply_coordinate {n : ℕ}
    (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (v : Fin n → ℂ) (i : Fin n) :
    L v i = ∑ j, L (Pi.single j 1) i * v j := by
  have hv : (∑ j, v j • Pi.single j 1) = v := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  calc
    L v i = L (∑ j, v j • Pi.single j 1) i := congrArg (fun w => L w i) hv.symm
    _ = _ := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring






theorem differentiableOn_inverse_weak_matrix_field {n : ℕ}
    {A Q : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {F : ℂ → Fin n → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : Continuous F) (hQ : ContDiff ℝ 1 Q)
    (hunit : ∀ z, IsUnit (Q z))
    (hQeq : ∀ z ∈ U, dbar Q z = A z * Q z)
    (hG : ∀ i, LocallyIntegrable (fun z => A z (F z) i) volume)
    (hweak : ∀ i (φ : ℂ → ℂ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ z, dbar φ z * F z i) = -∫ z, φ z * A z (F z) i) :
    DifferentiableOn ℂ (fun z => Ring.inverse (Q z) (F z)) U := by
  let R (z : ℂ) := Ring.inverse (Q z)
  have hR : ContDiff ℝ 1 R := contDiff_inverse_operator hQ hunit
  let q (i j : Fin n) (z : ℂ) := R z (Pi.single j 1) i
  have hq (i j : Fin n) : ContDiff ℝ 1 (q i j) := by
    have hev := ((ContinuousLinearMap.apply ℂ (Fin n → ℂ)
      (Pi.single j 1)).restrictScalars ℝ).contDiff.comp hR
    have hp := ((ContinuousLinearMap.proj i :
      (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff (n := 1)
    exact hp.comp hev
  have hdq (i j : Fin n) (z : ℂ) (hz : z ∈ U) :
      dbar (q i j) z = -R z (A z (Pi.single j 1)) i := by
    have hev := ((ContinuousLinearMap.apply ℂ (Fin n → ℂ)
      (Pi.single j 1)).restrictScalars ℝ).contDiff.comp hR
    have hRv : DifferentiableAt ℝ (fun w => R w (Pi.single j 1)) z :=
      hev.differentiable one_ne_zero z
    change dbar (fun w => (ContinuousLinearMap.proj i :
      (Fin n → ℂ) →L[ℂ] ℂ) (R w (Pi.single j 1))) z = _
    rw [dbar_clm_comp (ContinuousLinearMap.proj i) hRv,
      dbar_inverse_operator_apply hQ hunit (hQeq z hz)]
    rfl
  have hRF : Continuous (fun z => R z (F z)) := by
    have hres := (ContinuousLinearMap.restrictScalarsL ℂ
      (Fin n → ℂ) (Fin n → ℂ) ℝ ℝ).continuous.comp hR.continuous
    exact hres.clm_apply hF
  have hhol (i : Fin n) : DifferentiableOn ℂ (fun z => R z (F z) i) U := by
    have hc : Continuous (fun z => R z (F z) i) := (continuous_apply i).comp hRF
    apply differentiableOn_of_weak_dbar_eq_zero hc.locallyIntegrable hU hc.continuousOn
    intro φ hs hφU
    have hφ : ContDiff ℝ 1 (φ : ℂ → ℂ) := φ.smooth 1
    have hm (j : Fin n) : (∫ z, dbar φ z * (q i j z * F z j)) =
        -∫ z, φ z * (dbar (q i j) z * F z j + q i j z * A z (F z) j) :=
      weak_dbar_mul_C1 ((continuous_apply j).comp hF).locallyIntegrable
        (hG j) (hq i j) (hweak j) φ hφ hs hφU
    have hiL (j : Fin n) : Integrable (fun z => dbar φ z * (q i j z * F z j)) := by
      exact ((continuous_dbar hφ).mul ((hq i j).continuous.mul
        ((continuous_apply j).comp hF))).integrable_of_hasCompactSupport
          (hasCompactSupport_dbar hs).mul_right
    have hiR (j : Fin n) : Integrable
        (fun z => φ z * (dbar (q i j) z * F z j + q i j z * A z (F z) j)) := by
      have h1 : Integrable (fun z => (φ z * dbar (q i j) z) * F z j) :=
        ((hφ.continuous.mul (continuous_dbar (hq i j))).mul
        ((continuous_apply j).comp hF)).integrable_of_hasCompactSupport
          (hs.mul_right.mul_right)
      have h2 : Integrable (fun z => (φ z * q i j z) * A z (F z) j) := by
        simpa only [smul_eq_mul, Pi.mul_apply] using
          (hG j).integrable_smul_left_of_hasCompactSupport
            (hφ.continuous.mul (hq i j).continuous) hs.mul_right
      exact (h1.add h2).congr (ae_of_all _ fun z => by
        dsimp only [Pi.add_apply]
        ring)
    calc
      (∫ z, dbar φ z * R z (F z) i) =
          ∑ j, ∫ z, dbar φ z * (q i j z * F z j) := by
        simp_rw [operator_apply_coordinate (R _) (F _) i, Finset.mul_sum]
        exact integral_finsetSum _ (fun j _ => hiL j)
      _ = -∫ z, ∑ j, φ z *
          (dbar (q i j) z * F z j + q i j z * A z (F z) j) := by
        simp_rw [hm]
        rw [Finset.sum_neg_distrib]
        rw [integral_finsetSum _ (fun j _ => hiR j)]
      _ = 0 := by
        have hzero (z : ℂ) : (∑ j, φ z *
            (dbar (q i j) z * F z j + q i j z * A z (F z) j)) = 0 := by
          by_cases hz : z ∈ U
          · rw [← Finset.mul_sum, Finset.sum_add_distrib]
            simp_rw [hdq i _ z hz, neg_mul]
            rw [Finset.sum_neg_distrib]
            have h1 := operator_apply_coordinate ((R z).comp (A z)) (F z) i
            have h2 := operator_apply_coordinate (R z) (A z (F z)) i
            dsimp only [ContinuousLinearMap.comp_apply] at h1
            dsimp only [q]
            rw [← h1, ← h2]
            ring
          · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφU h))
            simp only [hφz, zero_mul, Finset.sum_const_zero]
        simp_rw [hzero, integral_zero, neg_zero]
  intro z hz
  exact differentiableWithinAt_pi.mpr (fun i => hhol i z hz)

end PoincareConjecture.M65Branch
