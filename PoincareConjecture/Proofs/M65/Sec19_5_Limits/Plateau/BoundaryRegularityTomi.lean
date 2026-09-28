import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityPlaneEquation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityIteration
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityDecay










set_option autoImplicit false

open Set Metric MeasureTheory Complex
open scoped Topology ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary





theorem plane_weighted_gradient_estimate {b : ℝ} (hb : 1 < b) (hb2 : b < 2)
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (f : LoopPlane → ℝ) (hf : Integrable f) {U : Set LoopPlane} (hU : IsOpen U)
    {R : ℝ} (hfs : Function.support f ⊆ closedBall (0 : LoopPlane) R)
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ φ : 𝓢(LoopPlane, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f z * φ z))
    {p : LoopPlane} (hp : p ∈ U) :
    ∃ r > 0, closedBall p r ⊆ U ∧ ∃ A ≥ 0, ∃ C > 0, ∀ x ∈ ball p r,
      Integrable (fun w => |f w| * ‖w - x‖ ^ (1 - b)) →
      IntegrableOn (fun z => ‖z - x‖ ^ (-b) * (∑ i : Fin 2, |d i z|)) (ball p r) ∧
      (∫ z in ball p r, ‖z - x‖ ^ (-b) * (∑ i : Fin 2, |d i z|)) ≤
        A + C * ∫ w, |f w| * ‖w - x‖ ^ (1 - b) := by
  let e := orthonormalBasisOneI.repr
  let W : ℂ → ℂ := fun z => (d 0 (e z) : ℂ) - I * (d 1 (e z) : ℂ)
  let h : ℂ → ℂ := fun z => (2 : ℂ)⁻¹ * (f (e z) : ℂ)
  let k : ℝ := ‖(2 : ℂ)⁻¹‖
  have hk : 0 < k := norm_pos_iff.mpr (inv_ne_zero (by norm_num))
  have hd (i : Fin 2) : LocallyIntegrable (fun z : ℂ => (d i (e z) : ℂ)) volume :=
    ((Lp.memLp (d i)).comp_measurePreserving
      orthonormalBasisOneI.measurePreserving_repr).ofReal.locallyIntegrable (by norm_num)
  have hW : LocallyIntegrable W volume := by
    simpa +instances only [W, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using!
      (hd 0).sub ((hd 1).smul I)
  have hfc : Integrable h :=
    ((orthonormalBasisOneI.measurePreserving_repr.integrable_comp_emb
      e.toHomeomorph.measurableEmbedding |>.mpr hf).ofReal).const_mul _
  have hhc : Function.support h ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    have hfz : f (e z) ≠ 0 := by
      intro hzero
      apply hz
      simp only [h, hzero, ofReal_zero, mul_zero]
    have hzR := hfs hfz
    simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hzR
  have hpC : e.symm p ∈ e ⁻¹' U := by
    change e (e.symm p) ∈ U
    simpa only [e.apply_symm_apply] using hp
  obtain ⟨r0, hr0, A, hA, C, hC, hgrad⟩ :=
    weak_gradient_weighted_estimate hb hb2 hW hfc hhc (hU.preimage e.continuous)
      (plane_weak_complex_gradient u d f hf hw heq) hpC
  obtain ⟨s, hs, hps⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  let r := min r0 s / 2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrr0 : r ≤ r0 := by
    have hmin := min_le_left r0 s
    dsimp only [r]
    linarith
  have hrs : r ≤ s := by
    have hmin := min_le_right r0 s
    dsimp only [r]
    linarith
  refine ⟨r, hr, (closedBall_subset_closedBall hrs).trans hps,
    2 * A, by positivity, 2 * C * k, by positivity, ?_⟩
  intro x hx hwgt
  have hxC : e.symm x ∈ ball (e.symm p) r0 := by
    rw [mem_ball, e.symm.isometry.dist_eq]
    exact (mem_ball.mp hx).trans_le hrr0
  have hweight_point (z : ℂ) : ‖h z‖ * ‖z - e.symm x‖ ^ (1 - b) =
      k * (|f (e z)| * ‖e z - x‖ ^ (1 - b)) := by
    have hn : ‖e z - x‖ = ‖z - e.symm x‖ := by
      simpa only [dist_eq_norm, e.apply_symm_apply] using e.isometry.dist_eq z (e.symm x)
    rw [hn]
    simp only [h, k, norm_mul, norm_real, Real.norm_eq_abs]
    ring
  have hwc : Integrable (fun z : ℂ => ‖h z‖ * ‖z - e.symm x‖ ^ (1 - b)) := by
    have hi := orthonormalBasisOneI.measurePreserving_repr.integrable_comp_emb
      e.toHomeomorph.measurableEmbedding |>.mpr hwgt
    exact (hi.const_mul k).congr (ae_of_all _ fun z => (hweight_point z).symm)
  have hweight_integral : (∫ z : ℂ, ‖h z‖ * ‖z - e.symm x‖ ^ (1 - b)) =
      k * ∫ z : LoopPlane, |f z| * ‖z - x‖ ^ (1 - b) := by
    simp_rw [hweight_point]
    rw [integral_const_mul]
    congr 1
    exact orthonormalBasisOneI.measurePreserving_repr.integral_comp
      e.toHomeomorph.measurableEmbedding (fun z => |f z| * ‖z - x‖ ^ (1 - b))
  obtain ⟨hWi, hWb⟩ := hgrad (e.symm x) hxC hwc
  let G : LoopPlane → ℝ := fun z =>
    ‖z - x‖ ^ (-b) * ‖(d 0 z : ℂ) - I * (d 1 z : ℂ)‖
  have hGpoint (z : ℂ) : G (e z) = ‖e.symm x - z‖ ^ (-b) * ‖W z‖ := by
    have hn : ‖e z - x‖ = ‖e.symm x - z‖ := by
      simpa only [dist_eq_norm, e.apply_symm_apply, norm_sub_rev] using
        e.isometry.dist_eq z (e.symm x)
    simp only [G, W, hn]
  have hGi : IntegrableOn G (ball p r0) := by
    rw [← orthonormalBasisOneI.measurePreserving_repr.integrableOn_comp_preimage
      e.toHomeomorph.measurableEmbedding, e.preimage_ball]
    exact hWi.congr (ae_of_all _ fun z => (hGpoint z).symm)
  have hGeq : (∫ z in ball p r0, G z) =
      ∫ z in ball (e.symm p) r0, ‖e.symm x - z‖ ^ (-b) * ‖W z‖ := by
    have hh := (orthonormalBasisOneI.measurePreserving_repr.restrict_preimage_emb
      e.toHomeomorph.measurableEmbedding (ball p r0)).integral_comp
        e.toHomeomorph.measurableEmbedding G
    rw [e.preimage_ball] at hh
    exact hh.symm.trans (integral_congr_ae (ae_of_all _ hGpoint))
  have hG0 (z : LoopPlane) : 0 ≤ G z := by dsimp only [G]; positivity
  have hGsmall := hGi.mono_set (ball_subset_ball hrr0)
  have hGbound : (∫ z in ball p r, G z) ≤
      A + C * (k * ∫ w, |f w| * ‖w - x‖ ^ (1 - b)) := by
    refine (setIntegral_mono_set hGi (ae_of_all _ hG0)
      (ball_subset_ball hrr0).eventuallyLE).trans ?_
    rw [hGeq]
    exact hWb.trans_eq (by rw [hweight_integral])
  have hpoint (z : LoopPlane) : ‖z - x‖ ^ (-b) * (∑ i : Fin 2, |d i z|) ≤ 2 * G z := by
    let w : ℂ := (d 0 z : ℂ) - I * (d 1 z : ℂ)
    have h0 : |d 0 z| ≤ ‖w‖ := by
      simpa only [w, sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        zero_mul, one_mul, sub_self, sub_zero] using abs_re_le_norm w
    have h1 : |d 1 z| ≤ ‖w‖ := by
      simpa only [w, sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
        zero_mul, one_mul, zero_add, zero_sub, abs_neg] using abs_im_le_norm w
    have hh := mul_le_mul_of_nonneg_left (add_le_add h0 h1)
      (Real.rpow_nonneg (norm_nonneg (z - x)) (-b))
    simpa only [Fin.sum_univ_two, G, w, mul_add, two_mul] using hh
  have hi : IntegrableOn (fun z => ‖z - x‖ ^ (-b) * (∑ i : Fin 2, |d i z|))
      (ball p r) := by
    apply (hGsmall.const_mul 2).mono'
    · have hm : Measurable (fun z : LoopPlane => ‖z - x‖ ^ (-b)) := by fun_prop
      simpa +instances only [Real.norm_eq_abs, Pi.mul_apply] using! (hm.aestronglyMeasurable.mul
        (Finset.aestronglyMeasurable_fun_sum _
          fun i _ => (Lp.aestronglyMeasurable (d i)).norm)).restrict
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint z
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z in ball p r, 2 * G z :=
      integral_mono_ae hi (hGsmall.const_mul 2) (ae_of_all _ hpoint)
    _ = 2 * ∫ z in ball p r, G z := integral_const_mul _ _
    _ ≤ 2 * (A + C * (k * ∫ w, |f w| * ‖w - x‖ ^ (1 - b))) :=
      mul_le_mul_of_nonneg_left hGbound (by norm_num)
    _ = _ := by ring





theorem weighted_gradient_tail {b ρ : ℝ} (hb : 1 < b) (hρ : 0 < ρ) :
    ∃ K ≥ 0, ∀ (x : LoopPlane) (u : Lp ℝ 2 (volume : Measure LoopPlane)),
      IntegrableOn (fun z => ‖z - x‖ ^ (-b) * |u z|) (closedBall x ρ)ᶜ ∧
      (∫ z in (closedBall x ρ)ᶜ, ‖z - x‖ ^ (-b) * |u z|) ≤ K + ‖u‖ ^ 2 := by
  let P : LoopPlane → ℝ := fun z => ‖z‖ ^ (-2 * b)
  have hPi : IntegrableOn P (closedBall (0 : LoopPlane) ρ)ᶜ := by
    let radial : ℝ → ℝ := (Ioi ρ).indicator (fun r => r ^ (-2 * b))
    have hbase : Integrable ((Ioi ρ).indicator (fun r : ℝ => r ^ (1 - 2 * b))) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : 1 - 2 * b < -1) hρ).integrable_indicator
        measurableSet_Ioi
    have hrad : Integrable (fun z : LoopPlane => radial ‖z‖) := by
      rw [integrable_fun_norm_addHaar volume]
      apply hbase.integrableOn.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      by_cases hρr : ρ < r
      · simp only [radial, mem_Ioi, indicator, hρr, ↓reduceIte,
          finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, pow_one, smul_eq_mul]
        rw [show 1 - 2 * b = 1 + (-2 * b) by ring, Real.rpow_add hr, Real.rpow_one]
      · simp only [radial, indicator, mem_Ioi, hρr, ↓reduceIte, smul_zero]
    rw [← integrable_indicator_iff isClosed_closedBall.measurableSet.compl]
    apply hrad.congr
    filter_upwards [] with z
    simp only [radial, P, indicator, mem_compl_iff, mem_closedBall_zero_iff, not_le, mem_Ioi]
  let K := ∫ z in (closedBall (0 : LoopPlane) ρ)ᶜ, P z
  have hK : 0 ≤ K := integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg z) _
  refine ⟨K, hK, ?_⟩
  intro x u
  let k : LoopPlane → ℝ := (closedBall (0 : LoopPlane) ρ)ᶜ.indicator P
  have hk : Integrable k := hPi.integrable_indicator isClosed_closedBall.measurableSet.compl
  have hshift : Integrable (fun z => k (z - x)) :=
    (measurePreserving_sub_right volume x).integrable_comp_emb
      (Homeomorph.subRight x).measurableEmbedding |>.mpr hk
  have hpoint_shift (z : LoopPlane) : k (z - x) =
      (closedBall x ρ)ᶜ.indicator (fun w => ‖w - x‖ ^ (-2 * b)) z := by
    simp only [k, P, indicator, mem_compl_iff, mem_closedBall, dist_eq_norm, sub_zero]
  have hwi : IntegrableOn (fun z => ‖z - x‖ ^ (-2 * b)) (closedBall x ρ)ᶜ := by
    rw [← integrable_indicator_iff isClosed_closedBall.measurableSet.compl]
    exact hshift.congr (ae_of_all _ hpoint_shift)
  have hwieq : (∫ z in (closedBall x ρ)ᶜ, ‖z - x‖ ^ (-2 * b)) = K := by
    rw [← integral_indicator isClosed_closedBall.measurableSet.compl]
    calc
      _ = ∫ z, k (z - x) := integral_congr_ae (ae_of_all _ fun z => (hpoint_shift z).symm)
      _ = ∫ z, k z := integral_sub_right_eq_self k x
      _ = K := integral_indicator isClosed_closedBall.measurableSet.compl
  have hui := (Lp.memLp u).integrable_sq
  have hbound (z : LoopPlane) : ‖z - x‖ ^ (-b) * |u z| ≤
      ‖z - x‖ ^ (-2 * b) + u z ^ 2 := by
    have hs : (‖z - x‖ ^ (-b)) ^ 2 = ‖z - x‖ ^ (-2 * b) := by
      rw [← Real.rpow_natCast (‖z - x‖ ^ (-b)) 2, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      ring
    nlinarith [sq_nonneg (‖z - x‖ ^ (-b) - |u z|), sq_abs (u z)]
  have hi : IntegrableOn (fun z => ‖z - x‖ ^ (-b) * |u z|) (closedBall x ρ)ᶜ := by
    apply (hwi.add hui.integrableOn).mono'
    · have hm : Measurable (fun z : LoopPlane => ‖z - x‖ ^ (-b)) := by fun_prop
      simpa +instances only [Pi.mul_apply, Real.norm_eq_abs] using!
        (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u).norm).restrict
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound z
  refine ⟨hi, ?_⟩
  have hsum : IntegrableOn (fun z => ‖z - x‖ ^ (-2 * b) + u z ^ 2)
      (closedBall x ρ)ᶜ := by
    simpa +instances only [Pi.add_apply] using! hwi.add hui.integrableOn
  calc
    _ ≤ ∫ z in (closedBall x ρ)ᶜ, ‖z - x‖ ^ (-2 * b) + u z ^ 2 :=
      integral_mono_ae hi hsum (ae_of_all _ hbound)
    _ = K + ∫ z in (closedBall x ρ)ᶜ, u z ^ 2 := by
      rw [integral_add hwi hui.integrableOn, hwieq]
    _ ≤ K + ∫ z, u z ^ 2 := add_le_add le_rfl
      (setIntegral_le_integral hui (ae_of_all _ fun z => sq_nonneg (u z)))
    _ = _ := by rw [EuclideanTranslationNative.scalarLp_norm_sq]

end PoincareConjecture.M65Boundary
