import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityGradient
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityC1
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityPotentialContinuity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace










set_option autoImplicit false

open Set MeasureTheory Complex Metric
open scoped Topology ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary

set_option maxHeartbeats 800000 in

private theorem complex_flux_test {K : ℕ} (A : Fin K → LoopPlane → ℝ)
    (v : Fin K → LoopPlane) (f : LoopPlane → ℝ) {U : Set LoopPlane}
    (hA : ∀ i, LocallyIntegrable (A i) volume) (hf : LocallyIntegrable f volume)
    (hweak : ∀ φ : 𝓢(LoopPlane, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, ∑ i : Fin K, fderiv ℝ φ z (v i) * A i z) = -(∫ z, φ z * f z))
    (φ : 𝓢(LoopPlane, ℂ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    (∫ z, ∑ i : Fin K, fderiv ℝ φ z (v i) * (A i z : ℂ)) =
      -(∫ z, φ z * (f z : ℂ)) := by
  let pr : 𝓢(LoopPlane, ℝ) := SchwartzMap.postcompCLM reCLM φ
  let pi : 𝓢(LoopPlane, ℝ) := SchwartzMap.postcompCLM imCLM φ
  have hprs : tsupport pr ⊆ tsupport φ := by
    apply closure_mono
    intro z hz hz0
    apply hz
    change (φ z).re = 0
    rw [hz0, zero_re]
  have hpis : tsupport pi ⊆ tsupport φ := by
    apply closure_mono
    intro z hz hz0
    apply hz
    change (φ z).im = 0
    rw [hz0, zero_im]
  have hpr : HasCompactSupport pr := hc.of_isClosed_subset (isClosed_tsupport _) hprs
  have hpi : HasCompactSupport pi := hc.of_isClosed_subset (isClosed_tsupport _) hpis
  have hrD (z w : LoopPlane) : fderiv ℝ pr z w = (fderiv ℝ φ z w).re := by
    exact congrArg (fun L : LoopPlane →L[ℝ] ℝ => L w)
      ((reCLM.hasFDerivAt.comp z (φ.differentiable z).hasFDerivAt).fderiv)
  have hiD (z w : LoopPlane) : fderiv ℝ pi z w = (fderiv ℝ φ z w).im := by
    exact congrArg (fun L : LoopPlane →L[ℝ] ℝ => L w)
      ((imCLM.hasFDerivAt.comp z (φ.differentiable z).hasFDerivAt).fderiv)
  have hleft : Integrable (fun z => ∑ i : Fin K, fderiv ℝ φ z (v i) * (A i z : ℂ)) := by
    apply integrable_finsetSum
    intro i _
    have hd : HasCompactSupport (∂_{v i} φ : 𝓢(LoopPlane, ℂ)) :=
      hc.of_isClosed_subset (isClosed_tsupport _)
        (SchwartzMap.tsupport_lineDerivOp_subset (v i) φ)
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, real_smul, mul_comm] using
      (hA i).integrable_smul_right_of_hasCompactSupport (∂_{v i} φ).continuous hd
  have hright : Integrable (fun z => φ z * (f z : ℂ)) := by
    simpa only [real_smul, mul_comm] using
      hf.integrable_smul_right_of_hasCompactSupport φ.continuous hc
  apply Complex.ext
  · have hL := reCLM.integral_comp_comm hleft
    have hR := reCLM.integral_comp_comm hright
    simp only [reCLM_apply] at hL hR
    rw [neg_re, ← hL, ← hR]
    simpa only [re_sum, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
      hrD, pr, SchwartzMap.postcompCLM_apply, reCLM_apply] using hweak pr hpr (hprs.trans hs)
  · have hL := imCLM.integral_comp_comm hleft
    have hR := imCLM.integral_comp_comm hright
    simp only [imCLM_apply] at hL hR
    rw [neg_im, ← hL, ← hR]
    simpa only [im_sum, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add,
      hiD, pi, SchwartzMap.postcompCLM_apply, imCLM_apply] using hweak pi hpi (hpis.trans hs)

private theorem complex_flux_transport {K : ℕ} (A : Fin K → LoopPlane → ℝ)
    (v : Fin K → LoopPlane) (f : LoopPlane → ℝ) {U : Set LoopPlane}
    (hA : ∀ i, LocallyIntegrable (A i) volume) (hf : LocallyIntegrable f volume)
    (hweak : ∀ φ : 𝓢(LoopPlane, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, ∑ i : Fin K, fderiv ℝ φ z (v i) * A i z) = -(∫ z, φ z * f z))
    (φ : 𝓢(ℂ, ℂ)) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ orthonormalBasisOneI.repr ⁻¹' U) :
    (∫ z, ∑ i : Fin K, fderiv ℝ φ z (orthonormalBasisOneI.repr.symm (v i)) *
      (A i (orthonormalBasisOneI.repr z) : ℂ)) =
      -(∫ z, φ z * (f (orthonormalBasisOneI.repr z) : ℂ)) := by
  let e := orthonormalBasisOneI.repr
  let ψ : 𝓢(LoopPlane, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm.toContinuousLinearEquiv φ
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e.symm.toHomeomorph
  have hψs : tsupport ψ ⊆ U := by
    have hsub : tsupport ψ ⊆ e.symm ⁻¹' tsupport φ := by
      apply closure_minimal
      · intro z hz
        exact subset_closure hz
      · exact (isClosed_tsupport _).preimage e.symm.continuous
    intro z hz
    have h := hs (hsub hz)
    change e (e.symm z) ∈ U at h
    simpa only [mem_preimage, LinearIsometryEquiv.apply_symm_apply] using h
  have hd (z w : LoopPlane) : fderiv ℝ ψ z w = fderiv ℝ φ (e.symm z) (e.symm w) := by
    exact congrArg (fun L : LoopPlane →L[ℝ] ℂ => L w)
      (((φ.differentiable (e.symm z)).hasFDerivAt.comp z
        e.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv)
  have h := complex_flux_test A v f hA hf hweak ψ hψc hψs
  have hL := orthonormalBasisOneI.measurePreserving_repr.integral_comp
    e.toHomeomorph.measurableEmbedding
    (fun z => ∑ i : Fin K, fderiv ℝ ψ z (v i) * (A i z : ℂ))
  have hR := orthonormalBasisOneI.measurePreserving_repr.integral_comp
    e.toHomeomorph.measurableEmbedding (fun z => ψ z * (f z : ℂ))
  rw [← hL, ← hR] at h
  simp_rw [hd] at h
  change (∫ z, ∑ i : Fin K, fderiv ℝ φ (e.symm (e z)) (e.symm (v i)) *
    (A i (e z) : ℂ)) = -(∫ z, φ (e.symm (e z)) * (f (e z) : ℂ)) at h
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h




theorem plane_weak_complex_gradient
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (f : LoopPlane → ℝ) (hf : Integrable f) {U : Set LoopPlane}
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ φ : 𝓢(LoopPlane, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f z * φ z))
    (φ : 𝓢(ℂ, ℂ)) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ orthonormalBasisOneI.repr ⁻¹' U) :
    (∫ z, M65Branch.dbar φ z *
      ((d 0 (orthonormalBasisOneI.repr z) : ℂ) -
        I * (d 1 (orthonormalBasisOneI.repr z) : ℂ))) =
      -(∫ z, φ z * ((2 : ℂ)⁻¹ * (f (orthonormalBasisOneI.repr z) : ℂ))) := by
  let e := orthonormalBasisOneI.repr
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hd (i : Fin 2) := (Lp.memLp (d i)).locallyIntegrable (by norm_num)
  have hdc (i : Fin 2) : LocallyIntegrable (fun z : ℂ => (d i (e z) : ℂ)) volume :=
    ((Lp.memLp (d i)).comp_measurePreserving
      orthonormalBasisOneI.measurePreserving_repr).ofReal.locallyIntegrable (by norm_num)
  have hfirst (i : Fin 2) (ψ : 𝓢(ℂ, ℂ)) (hψ : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ e ⁻¹' U) :
      (∫ z, fderiv ℝ ψ z (orthonormalBasisOneI i) * (u (e z) : ℂ)) =
        -(∫ z, ψ z * (d i (e z) : ℂ)) := by
    have h := complex_flux_transport (K := 1) (fun _ => u)
      (fun _ => EuclideanSpace.single i 1) (d i) (fun _ => hu) (hd i)
      (fun θ _ _ => ?_) ψ hψ hψs
    · simpa only [Fin.sum_univ_one, OrthonormalBasis.repr_symm_single] using h
    · have hθ := hw i θ
      rw [DeTurckDomainRegularityNative.inner_schwartz] at hθ
      simp only [Fin.sum_univ_one]
      have hleft : (∫ z, fderiv ℝ θ z (EuclideanSpace.single i 1) * u z) =
          ∫ z, u z * fderiv ℝ θ z (EuclideanSpace.single i 1) :=
        integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
      have hright : (∫ z, θ z * d i z) = ∫ z, d i z * θ z :=
        integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
      rw [hleft, hright]
      linarith only [hθ]
  apply weak_laplacian_complex_gradient (u := fun z => (u (e z) : ℂ))
    (hdc 0) (hdc 1) ?_ ?_ φ hc hs
  · intro ψ hψ hψs
    have h0 := hfirst 0 ψ hψ hψs
    have h1 := hfirst 1 ψ hψ hψs
    simp only [coe_orthonormalBasisOneI, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h0 h1
    constructor
    · simpa only [neg_neg] using (congrArg Neg.neg h0).symm
    · simpa only [neg_neg] using (congrArg Neg.neg h1).symm
  · intro ψ hψ hψs
    have h := complex_flux_transport (fun i => d i) (fun i => EuclideanSpace.single i 1)
      f hd hf.locallyIntegrable (fun θ hθ hθs => ?_) ψ hψ hψs
    · simpa only [Fin.sum_univ_two, OrthonormalBasis.repr_symm_single,
        coe_orthonormalBasisOneI, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] using h
    · have hi (i : Fin 2) : Integrable
          (fun z => d i z * fderiv ℝ θ z (EuclideanSpace.single i 1)) :=
        (Lp.memLp (d i)).integrable_mul
          ((∂_{EuclideanSpace.single i (1 : ℝ)} θ).memLp 2 volume)
      have hθeq := heq θ hθ hθs
      simp only [DeTurckDomainRegularityNative.inner_schwartz,
        SchwartzMap.lineDerivOp_apply_eq_fderiv, Fin.sum_univ_two] at hθeq ⊢
      simp_rw [mul_comm (fderiv ℝ θ _ _) (d _ _), mul_comm (θ _) (f _)]
      rw [integral_add (hi 0) (hi 1)]
      exact hθeq





theorem plane_weak_gradient_decomposition
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
    {x : LoopPlane} (hx : x ∈ U) :
    ∃ r > 0, ∃ H : ℂ → ℂ, ContDiff ℝ ∞ H ∧
      DifferentiableOn ℂ H (ball (orthonormalBasisOneI.repr.symm x) r) ∧
      ∀ᵐ z ∂volume.restrict (ball (orthonormalBasisOneI.repr.symm x) r),
        (d 0 (orthonormalBasisOneI.repr z) : ℂ) -
          I * (d 1 (orthonormalBasisOneI.repr z) : ℂ) =
            M65Branch.cauchyOperator
              (fun w => (2 : ℂ)⁻¹ * (f (orthonormalBasisOneI.repr w) : ℂ)) z + H z := by
  let e := orthonormalBasisOneI.repr
  have hd (i : Fin 2) : LocallyIntegrable (fun z : ℂ => (d i (e z) : ℂ)) volume :=
    ((Lp.memLp (d i)).comp_measurePreserving
      orthonormalBasisOneI.measurePreserving_repr).ofReal.locallyIntegrable (by norm_num)
  have hW : LocallyIntegrable (fun z : ℂ => (d 0 (e z) : ℂ) - I * (d 1 (e z) : ℂ))
      volume := by
    simpa +instances only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using!
      (hd 0).sub ((hd 1).smul I)
  have hfc : Integrable (fun w : ℂ => (f (e w) : ℂ)) :=
    (orthonormalBasisOneI.measurePreserving_repr.integrable_comp_emb
      e.toHomeomorph.measurableEmbedding |>.mpr hf).ofReal
  apply exists_cauchy_decomposition hW (hfc.const_mul _) (R := R) ?_
    (hU.preimage e.continuous) (plane_weak_complex_gradient u d f hf hw heq) ?_
  · intro z hz
    have hfz : f (e z) ≠ 0 := by
      intro hzero
      apply hz
      simp only [hzero, ofReal_zero, mul_zero]
    have h := hfs hfz
    simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using h
  · change e (e.symm x) ∈ U
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hx






theorem plane_weak_C1_of_weight
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
    (v : LoopPlane → ℝ) (hv : ContinuousOn v U)
    (huv : (u : LoopPlane → ℝ) =ᵐ[volume.restrict U] v)
    {a B : ℝ} (ha : 1 < a)
    (hweight : ∀ x ∈ U, Integrable (fun z => |f z| * ‖x - z‖ ^ (-a)))
    (hbound : ∀ x ∈ U, (∫ z, |f z| * ‖x - z‖ ^ (-a)) ≤ B) :
    ContDiffOn ℝ 1 v U := by
  let e := orthonormalBasisOneI.repr
  let h : ℂ → ℂ := fun z => (2 : ℂ)⁻¹ * (f (e z) : ℂ)
  let k : ℝ := ‖(2 : ℂ)⁻¹‖
  have hfc : Integrable h :=
    ((orthonormalBasisOneI.measurePreserving_repr.integrable_comp_emb
      e.toHomeomorph.measurableEmbedding |>.mpr hf).ofReal).const_mul _
  have hwC (x : ℂ) (hx : x ∈ e ⁻¹' U) :
      Integrable (fun w => ‖h w‖ * ‖x - w‖ ^ (-a)) ∧
        (∫ w, ‖h w‖ * ‖x - w‖ ^ (-a)) ≤ k * B := by
    have hpoint (w : ℂ) : ‖h w‖ * ‖x - w‖ ^ (-a) =
        k * (|f (e w)| * ‖e x - e w‖ ^ (-a)) := by
      rw [← e.map_sub, e.norm_map]
      simp only [h, k, norm_mul, norm_real, Real.norm_eq_abs]
      ring
    have hi := orthonormalBasisOneI.measurePreserving_repr.integrable_comp_emb
      e.toHomeomorph.measurableEmbedding |>.mpr (hweight (e x) hx)
    have hid := orthonormalBasisOneI.measurePreserving_repr.integral_comp
      e.toHomeomorph.measurableEmbedding (fun z => |f z| * ‖e x - z‖ ^ (-a))
    constructor
    · exact (hi.const_mul k).congr (ae_of_all _ fun w => (hpoint w).symm)
    · simp_rw [hpoint]
      rw [integral_const_mul, hid]
      exact mul_le_mul_of_nonneg_left (hbound (e x) hx) (norm_nonneg _)
  have hpot : ContinuousOn (M65Branch.cauchyOperator h) (e ⁻¹' U) :=
    continuousOn_cauchy_of_uniform_weight ha hfc
      (fun x hx => (hwC x hx).1) (fun x hx => (hwC x hx).2)
  intro p hp
  obtain ⟨r, hr, H, hH, _hhol, hAE⟩ :=
    plane_weak_gradient_decomposition u d f hf hU hfs hw heq hp
  let V : Set LoopPlane := U ∩ e.symm ⁻¹' ball (e.symm p) r
  have hV : IsOpen V := hU.inter (isOpen_ball.preimage e.symm.continuous)
  have hpV : p ∈ V := ⟨hp, mem_ball_self hr⟩
  let W : LoopPlane → ℂ := fun z => M65Branch.cauchyOperator h (e.symm z) + H (e.symm z)
  let g : Fin 2 → LoopPlane → ℝ := ![fun z => (W z).re, fun z => -(W z).im]
  have hW : ContinuousOn W V := by
    apply ContinuousOn.add
    · apply hpot.comp e.symm.continuous.continuousOn
      intro z hz
      change e (e.symm z) ∈ U
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hz.1
    · exact (hH.continuous.comp e.symm.continuous).continuousOn
  have hg (i : Fin 2) : ContinuousOn (g i) V := by
    fin_cases i
    · exact continuous_re.comp_continuousOn hW
    · exact (continuous_im.comp_continuousOn hW).neg
  have hglobal := (ae_restrict_iff' measurableSet_ball).mp hAE
  have htransport := orthonormalBasisOneI.measurePreserving_repr_symm.quasiMeasurePreserving.ae
    hglobal
  have hdg (i : Fin 2) : (d i : LoopPlane → ℝ) =ᵐ[volume.restrict V] g i := by
    filter_upwards [ae_restrict_of_ae htransport, ae_restrict_mem hV.measurableSet]
      with z hz hzV
    have hequal := hz hzV.2
    change (d 0 (e (e.symm z)) : ℂ) - I * (d 1 (e (e.symm z)) : ℂ) = W z at hequal
    rw [e.apply_symm_apply] at hequal
    fin_cases i
    · change d 0 z = (W z).re
      have ht := congrArg Complex.re hequal
      simpa only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        zero_mul, one_mul, sub_self, sub_zero] using ht
    · change d 1 z = -(W z).im
      have ht := congrArg (fun w : ℂ => -w.im) hequal
      simpa only [sub_im, ofReal_im, mul_im,
        I_re, I_im, ofReal_re,
        zero_mul, one_mul, zero_add, zero_sub, neg_neg] using ht
  have hC1 := (weak_pair_contDiffOn u d
    (by simpa only [EuclideanSpace.basisFun_apply] using hw)
    hV v g (hv.mono inter_subset_left) hg
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left huv) hdg).1
  exact ((hC1 p hpV).contDiffAt (hV.mem_nhds hpV)).contDiffWithinAt

end PoincareConjecture.M65Boundary
