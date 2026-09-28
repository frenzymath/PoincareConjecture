import PoincareConjecture.Proofs.M76.Mathlib.RadialSimplex
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open Set NormedSpace

namespace Complex



theorem linearIndependent_one_circleExp {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    LinearIndependent ℝ ((↑) : ↥({(1 : ℂ), (Circle.exp theta : ℂ)} : Set ℂ) → ℂ) := by
  change LinearIndepOn ℝ id {(1 : ℂ), (Circle.exp theta : ℂ)}
  apply linearIndepOn_id_pair one_ne_zero
  intro a ha
  have hi := congrArg Complex.im ha
  have hsin := Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2
  simp only [smul_im, one_im, smul_zero, Circle.coe_exp, exp_ofReal_mul_I_im] at hi
  linarith



theorem im_circleExp_neg_mul (theta : ℝ) (z : ℂ) :
    ((Circle.exp (-theta) : ℂ) * z).im = ‖z‖ * Real.sin (z.arg - theta) := by
  calc
    ((Circle.exp (-theta) : ℂ) * z).im = Real.cos theta * z.im - Real.sin theta * z.re := by
      simp only [mul_im, Circle.coe_exp, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
        Real.cos_neg, Real.sin_neg]
      ring
    _ = ‖z‖ * Real.sin (z.arg - theta) := by
      rw [← norm_mul_sin_arg z, ← norm_mul_cos_arg z, Real.sin_sub]
      ring



theorem arg_mem_Icc_of_short_sector {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    {z : ℂ} (hz : z ≠ 0) (him : 0 ≤ z.im)
    (hrot : ((Circle.exp (-theta) : ℂ) * z).im ≤ 0) : z.arg ∈ Icc (0 : ℝ) theta := by
  refine ⟨arg_nonneg_iff.mpr him, ?_⟩
  rw [im_circleExp_neg_mul] at hrot
  by_contra hle
  have hthetaarg : theta < z.arg := lt_of_not_ge hle
  have hsin : 0 < Real.sin (z.arg - theta) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hthetaarg) (by
      have harg := arg_le_pi z
      linarith [htheta.1])
  exact (not_lt_of_ge hrot) (mul_pos (norm_pos_iff.mpr hz) hsin)



theorem segment_one_circleExp_subset_slitPlane {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    segment ℝ (1 : ℂ) (Circle.exp theta) ⊆ slitPlane := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1, mem_slitPlane_iff]
  · apply Or.inr
    have hsin := Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    simpa only [add_im, smul_im, one_im, smul_zero, zero_add, Circle.coe_exp,
      exp_ofReal_mul_I_im, smul_eq_mul, mul_zero] using (mul_pos hbpos hsin).ne'



theorem arg_mem_Icc_of_mem_segment_one_circleExp {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) {z : ℂ}
    (hz : z ∈ segment ℝ (1 : ℂ) (Circle.exp theta)) : z.arg ∈ Icc (0 : ℝ) theta := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (segment_one_circleExp_subset_slitPlane htheta hz)
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  apply arg_mem_Icc_of_short_sector htheta hz0
  · simpa only [add_im, smul_im, one_im, smul_zero, zero_add, Circle.coe_exp,
      exp_ofReal_mul_I_im, smul_eq_mul, mul_zero] using
      mul_nonneg hb (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1.le htheta.2.le)
  · have he : ((Circle.exp (-theta) : ℂ) *
        (a • (1 : ℂ) + b • (Circle.exp theta : ℂ))).im = -a * Real.sin theta := by
      simp only [mul_im, add_im, smul_im, one_im, add_re, smul_re, one_re, smul_eq_mul,
        Circle.coe_exp, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
      ring
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
      (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1.le htheta.2.le)



theorem arg_image_segment_one_circleExp {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    Complex.arg '' segment ℝ (1 : ℂ) (Circle.exp theta) = Icc (0 : ℝ) theta := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact arg_mem_Icc_of_mem_segment_one_circleExp htheta hz
  · intro phi hphi
    let f : ℝ → ℂ := fun t => (1 - t) • (1 : ℂ) + t • (Circle.exp theta : ℂ)
    have hfseg : MapsTo f (Icc (0 : ℝ) 1) (segment ℝ (1 : ℂ) (Circle.exp theta)) := by
      intro t ht
      exact ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, rfl⟩
    have hf : Continuous f := by fun_prop
    have harg : ContinuousOn (Complex.arg ∘ f) (Icc (0 : ℝ) 1) :=
      continuousOn_arg.comp hf.continuousOn
        (fun t ht => segment_one_circleExp_subset_slitPlane htheta (hfseg ht))
    have hends : phi ∈ Icc ((Complex.arg ∘ f) 0) ((Complex.arg ∘ f) 1) := by
      simpa only [Function.comp_apply, f, sub_zero, one_smul, zero_smul, add_zero, arg_one,
        sub_self, zero_add, Circle.arg_exp (by linarith [Real.pi_pos, htheta.1]) htheta.2.le]
        using hphi
    obtain ⟨t, ht, htf⟩ := intermediate_value_Icc zero_le_one harg hends
    exact ⟨f t, hfseg ht, htf⟩



theorem normalize_eq_circleExp_arg {z : ℂ} (hz : z ≠ 0) :
    NormedSpace.normalize z = (Circle.exp z.arg : ℂ) := by
  have hpolar : ‖z‖ • (Circle.exp z.arg : ℂ) = z := by
    simpa only [Circle.coe_exp, real_smul] using norm_mul_exp_arg_mul_I z
  calc
    NormedSpace.normalize z = ‖z‖⁻¹ • (‖z‖ • (Circle.exp z.arg : ℂ)) :=
      congrArg (fun x : ℂ => ‖z‖⁻¹ • x) hpolar.symm
    _ = (Circle.exp z.arg : ℂ) := inv_smul_smul₀ (norm_ne_zero_iff.mpr hz) _




theorem normalize_image_segment_one_circleExp {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    NormedSpace.normalize '' segment ℝ (1 : ℂ) (Circle.exp theta) =
      (fun phi => (Circle.exp phi : ℂ)) '' Icc (0 : ℝ) theta := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.arg, arg_mem_Icc_of_mem_segment_one_circleExp htheta hz,
      (normalize_eq_circleExp_arg
        (slitPlane_ne_zero (segment_one_circleExp_subset_slitPlane htheta hz))).symm⟩
  · rintro _ ⟨phi, hphi, rfl⟩
    obtain ⟨z, hz, harg⟩ := (arg_image_segment_one_circleExp htheta).symm.subset hphi
    refine ⟨z, hz, ?_⟩
    rw [normalize_eq_circleExp_arg
      (slitPlane_ne_zero (segment_one_circleExp_subset_slitPlane htheta hz)), harg]



theorem normalize_circle_mul (a : Circle) (z : ℂ) :
    NormedSpace.normalize ((a : ℂ) * z) = (a : ℂ) * NormedSpace.normalize z := by
  simp only [NormedSpace.normalize, norm_mul, Circle.norm_coe, one_mul, mul_smul_comm]



theorem circleExp_mul_image_segment (a b : ℝ) :
    (fun z : ℂ => (Circle.exp a : ℂ) * z) ''
      segment ℝ (1 : ℂ) (Circle.exp (b - a)) =
        segment ℝ (Circle.exp a : ℂ) (Circle.exp b) := by
  have h := image_segment ℝ (rotation (Circle.exp a)).toLinearEquiv.toAffineMap
    (1 : ℂ) (Circle.exp (b - a))
  change (fun z : ℂ => (Circle.exp a : ℂ) * z) '' _ =
    segment ℝ ((Circle.exp a : ℂ) * 1)
      ((Circle.exp a : ℂ) * (Circle.exp (b - a) : ℂ)) at h
  simpa only [mul_one, ← Circle.coe_mul, ← Circle.exp_add, add_sub_cancel] using h




theorem linearIndependent_circleExp_pair {a b : ℝ} (hab : a < b) (hba : b - a < Real.pi) :
    LinearIndependent ℝ ((↑) : ↥({(Circle.exp a : ℂ), (Circle.exp b : ℂ)} : Set ℂ) → ℂ) := by
  change LinearIndepOn ℝ id ({(Circle.exp a : ℂ), (Circle.exp b : ℂ)} : Set ℂ)
  have h : LinearIndepOn ℝ id ({(1 : ℂ), (Circle.exp (b - a) : ℂ)} : Set ℂ) :=
    linearIndependent_one_circleExp ⟨sub_pos.mpr hab, hba⟩
  have hr := h.id_imageₛ (f := (rotation (Circle.exp a)).toLinearEquiv.toLinearMap)
    (rotation (Circle.exp a)).injective.injOn
  simpa only [image_pair, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    rotation_apply, mul_one, ← Circle.coe_mul, ← Circle.exp_add, add_sub_cancel] using hr





theorem normalize_image_segment_circleExp {a b : ℝ} (hab : a < b)
    (hba : b - a < Real.pi) :
    NormedSpace.normalize '' segment ℝ (Circle.exp a : ℂ) (Circle.exp b) =
      (fun phi => (Circle.exp phi : ℂ)) '' Icc a b := by
  rw [← circleExp_mul_image_segment a b, image_image]
  simp_rw [normalize_circle_mul]
  rw [← image_image, normalize_image_segment_one_circleExp ⟨sub_pos.mpr hab, hba⟩,
    image_image]
  simp only [← Circle.coe_mul, ← Circle.exp_add]
  apply Subset.antisymm
  · rintro _ ⟨phi, hphi, rfl⟩
    exact ⟨a + phi, ⟨by linarith [hphi.1], by linarith [hphi.2]⟩, rfl⟩
  · rintro _ ⟨phi, hphi, rfl⟩
    refine ⟨phi - a, ⟨sub_nonneg.mpr hphi.1, sub_le_sub_right hphi.2 a⟩, ?_⟩
    simp only [add_sub_cancel]

end Complex
