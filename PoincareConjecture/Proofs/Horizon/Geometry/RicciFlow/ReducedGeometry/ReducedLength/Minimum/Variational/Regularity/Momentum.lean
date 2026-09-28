import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Primitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff

namespace PoincareConjecture.ReducedLengthMinimum.Variational

theorem smooth_zero_integral_compact_primitive {a b : ℝ} (hab : a < b)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d) (hds : tsupport d ⊆ Ioo a b)
    (hdint : (∫ s in a..b, d s) = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo a b ∧ deriv f = d := by
  obtain ⟨f, hf, hfa, hfb, hfd⟩ := smooth_primitive_fixed_endpoints hab 0 0 d hd
  have hderiv (s : ℝ) : HasDerivAt f (d s) s := by
    simpa only [hdint, sub_zero, smul_zero, add_zero] using hfd s
  have hleft {s : ℝ} (hs : s ≤ a) : f s = 0 :=
    (primitive_eq_left_of_support hd.continuous hderiv hds hs).trans hfa
  have hright {s : ℝ} (hs : b ≤ s) : f s = 0 :=
    (primitive_eq_right_of_support hd.continuous hderiv hds hs).trans hfb
  have hsupp : Function.support f ⊆ Icc a b := by
    intro s hs
    constructor
    · by_contra h
      exact hs (hleft (le_of_not_ge h))
    · by_contra h
      exact hs (hright (le_of_not_ge h))
  have htsupp : tsupport f ⊆ Icc a b := closure_minimal hsupp isClosed_Icc
  have hnot (t : ℝ) (ht : t ∉ tsupport d) (hft : f t = 0) : t ∉ tsupport f := by
    have hg : f =ᶠ[𝓝 t] fun _ ↦ 0 := by
      simpa only [hft] using primitive_constant_germ hderiv ht
    intro ht'
    have hfreq := mem_closure_iff_frequently.mp ht'
    obtain ⟨s, hs, hzero⟩ := (hfreq.and_eventually hg).exists
    exact hs hzero
  have ha : a ∉ tsupport f := hnot a
    (fun h ↦ (lt_irrefl a) (hds h).1) hfa
  have hb : b ∉ tsupport f := hnot b
    (fun h ↦ (lt_irrefl b) (hds h).2) hfb
  refine ⟨f, hf, isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) htsupp, ?_, ?_⟩
  · intro s hs
    exact ⟨lt_of_le_of_ne (htsupp hs).1 (fun h ↦ ha (h ▸ hs)),
      lt_of_le_of_ne (htsupp hs).2 (fun h ↦ hb (h ▸ hs))⟩
  · funext s
    exact (hderiv s).deriv

theorem scalar_primitive_integration_by_parts {a b : ℝ}
    {Q φ : ℝ → ℝ} (hQ : IntervalIntegrable Q volume a b)
    (hφ : ContDiff ℝ ∞ φ) (hφa : φ a = 0) (hφb : φ b = 0) :
    (∫ s in a..b, deriv φ s * (∫ r in a..s, Q r)) =
      -(∫ s in a..b, φ s * Q s) := by
  have hH := hQ.absolutelyContinuousOnInterval_intervalIntegral (c := a) left_mem_uIcc
  have hφac : AbsolutelyContinuousOnInterval φ a b :=
    (hφ.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hparts := hH.integral_mul_deriv_eq_deriv_mul hφac
  have heq : (∫ s in a..b, deriv (fun t ↦ ∫ r in a..t, Q r) s * φ s) =
      ∫ s in a..b, Q s * φ s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hQ.ae_hasDerivAt_integral] with s hs hmem
    rw [(hs (uIoc_subset_uIcc hmem) a left_mem_uIcc).deriv]
  rw [heq, hφa, hφb] at hparts
  simpa only [mul_zero, zero_mul, sub_self, zero_sub, mul_comm] using hparts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem weak_derivative_zero_ae_const {a b : ℝ} (hab : a < b)
    (R : ℝ → E) (hR : IntervalIntegrable R volume a b)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ s in a..b, deriv φ s • R s) = 0) :
    ∃ c : E, ∀ᵐ s ∂volume.restrict (Icc a b), R s = c := by
  obtain ⟨β, hβ, hβc, hβs, hβint⟩ := exists_interior_normalized_bump hab
  let c : E := ∫ s in a..b, β s • R s
  have htest (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ Ioo a b) :
      (∫ s in a..b, ψ s • (R s - c)) = 0 := by
    let z : ℝ := ∫ s in a..b, ψ s
    let d : ℝ → ℝ := fun s ↦ ψ s - z * β s
    have hd : ContDiff ℝ ∞ d := hψ.sub (contDiff_const.mul hβ)
    have hds : tsupport d ⊆ Ioo a b :=
      (tsupport_sub ψ (fun s ↦ z * β s)).trans
        (union_subset hψs (tsupport_mul_subset_right.trans hβs))
    have hdint : (∫ s in a..b, d s) = 0 := by
      change (∫ s in a..b, ψ s - z * β s) = 0
      rw [intervalIntegral.integral_sub (f := ψ) (g := fun s ↦ z * β s)
        (hψ.continuous.intervalIntegrable a b)
        (((continuous_const (y := z)).mul hβ.continuous).intervalIntegrable a b),
        intervalIntegral.integral_const_mul, hβint, mul_one]
      exact sub_self z
    obtain ⟨f, hf, hfc, hfs, hfderiv⟩ :=
      smooth_zero_integral_compact_primitive hab d hd hds hdint
    have hzero := hweak f hf hfc hfs
    rw [hfderiv] at hzero
    have hintψ : IntervalIntegrable (fun s ↦ ψ s • R s) volume a b :=
      hR.continuousOn_smul hψ.continuous.continuousOn
    have hintβ : IntervalIntegrable (fun s ↦ β s • R s) volume a b :=
      hR.continuousOn_smul hβ.continuous.continuousOn
    have hmain : (∫ s in a..b, ψ s • R s) - z • c = 0 := by
      simp only [d, sub_smul, mul_smul] at hzero
      rw [intervalIntegral.integral_sub (f := fun s ↦ ψ s • R s)
        (g := fun s ↦ z • (β s • R s)) hintψ (hintβ.smul z),
        intervalIntegral.integral_smul] at hzero
      exact hzero
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub (f := fun s ↦ ψ s • R s)
      (g := fun s ↦ ψ s • c) hintψ
      ((hψ.continuous.smul (continuous_const (y := c))).intervalIntegrable a b),
      intervalIntegral.integral_smul_const]
    exact hmain
  have hRIoo : IntegrableOn R (Ioo a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hR
  have hlocal : LocallyIntegrableOn (fun s ↦ R s - c) (Ioo a b) volume :=
    hRIoo.locallyIntegrableOn.sub (locallyIntegrableOn_const c)
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    (fun ψ hψ hψc hψs ↦ by
      rw [← intervalIntegral.integral_eq_integral_of_support_subset
        (f := fun s ↦ ψ s • (R s - c))
        ((Function.support_smul_subset_left ψ (fun s ↦ R s - c)).trans
          ((subset_tsupport ψ).trans (hψs.trans Ioo_subset_Ioc_self)))]
      exact htest ψ hψ hψc hψs)
  refine ⟨c, ?_⟩
  rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae] with s hs hmem
  exact sub_eq_zero.mp (hs hmem)

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem primitive_integration_by_parts {a b : ℝ}
    {Q : ℝ → F} {φ : ℝ → ℝ} (hQ : IntervalIntegrable Q volume a b)
    (hφ : ContDiff ℝ ∞ φ) (hφa : φ a = 0) (hφb : φ b = 0) :
    (∫ s in a..b, deriv φ s • (∫ r in a..s, Q r)) =
      -(∫ s in a..b, φ s • Q s) := by
  have hHcont : ContinuousOn (fun s ↦ ∫ r in a..s, Q r) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hQ left_mem_uIcc
  have hL : IntervalIntegrable
      (fun s ↦ deriv φ s • (∫ r in a..s, Q r)) volume a b :=
    ((hφ.continuous_deriv (by norm_num)).intervalIntegrable a b).smul_continuousOn hHcont
  have hR : IntervalIntegrable (fun s ↦ φ s • Q s) volume a b :=
    hQ.continuousOn_smul hφ.continuous.continuousOn
  apply ext_inner_left ℝ
  intro z
  let l : F →L[ℝ] ℝ := innerSL ℝ z
  have hQl : IntervalIntegrable (fun s ↦ l (Q s)) volume a b :=
    ⟨l.integrable_comp hQ.1, l.integrable_comp hQ.2⟩
  have hprimitive (s : ℝ) (hs : s ∈ uIcc a b) :
      l (∫ r in a..s, Q r) = ∫ r in a..s, l (Q r) :=
    (l.intervalIntegral_comp_comm (hQ.mono_set (uIcc_subset_uIcc left_mem_uIcc hs))).symm
  change l (∫ s in a..b, deriv φ s • (∫ r in a..s, Q r)) =
    l (-(∫ s in a..b, φ s • Q s))
  rw [map_neg, ← l.intervalIntegral_comp_comm hL, ← l.intervalIntegral_comp_comm hR]
  simp only [map_smul, smul_eq_mul]
  calc
    _ = ∫ s in a..b, deriv φ s * (∫ r in a..s, l (Q r)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact congrArg (fun v : ℝ ↦ deriv φ s * v) (hprimitive s hs)
    _ = _ := scalar_primitive_integration_by_parts hQl hφ hφa hφb

theorem weak_momentum_primitive {a b : ℝ} (hab : a < b)
    (P Q : ℝ → F) (hP : IntervalIntegrable P volume a b)
    (hQ : IntervalIntegrable Q volume a b)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ s in a..b, deriv φ s • P s) =
        -(∫ s in a..b, φ s • Q s)) :
    ∃ c : F, ∀ᵐ s ∂volume.restrict (Icc a b),
      P s = c + ∫ r in a..s, Q r := by
  let H : ℝ → F := fun s ↦ ∫ r in a..s, Q r
  have hHcont : ContinuousOn H (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hQ left_mem_uIcc
  obtain ⟨c, hc⟩ := weak_derivative_zero_ae_const hab (fun s ↦ P s - H s)
    (hP.sub hHcont.intervalIntegrable) (fun φ hφ hφc hφs ↦ by
      have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ (lt_irrefl a) (hφs h).1)
      have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ (lt_irrefl b) (hφs h).2)
      have hD : Continuous (deriv φ) := hφ.continuous_deriv (by norm_num)
      simp_rw [smul_sub]
      rw [intervalIntegral.integral_sub (f := fun s ↦ deriv φ s • P s)
        (g := fun s ↦ deriv φ s • H s)
        (hP.continuousOn_smul hD.continuousOn)
        ((hD.intervalIntegrable a b).smul_continuousOn hHcont),
        hweak φ hφ hφc hφs]
      change -(∫ s in a..b, φ s • Q s) -
        (∫ s in a..b, deriv φ s • (∫ r in a..s, Q r)) = 0
      rw [primitive_integration_by_parts hQ hφ hφa hφb, sub_self])
  refine ⟨c, hc.mono ?_⟩
  intro s hs
  exact sub_eq_iff_eq_add.mp hs

end InnerProduct

end PoincareConjecture.ReducedLengthMinimum.Variational
