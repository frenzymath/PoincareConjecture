import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveH1Compactness
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem l2_sq_sub {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f g : X → E} (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hx hxf hxg
  simp only [hx, Pi.sub_apply, hxf, hxg]

omit [CompleteSpace E] in
private theorem l2_tendsto_of_integral_sq {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : ℕ → X → E} {u : X → E} (hf : ∀ j, MemLp (f j) 2 mu) (hu : MemLp u 2 mu)
    (hlim : Tendsto (fun j => ∫ x, ‖f j x - u x‖ ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hu.toLp u)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun j => ‖(hf j).toLp (f j) - hu.toLp u‖ ^ 2) atTop (𝓝 0) := by
    simpa only [l2_sq_sub] using hlim
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt

omit [CompleteSpace E] in
private theorem l2_pair_integral_tendsto {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : ℕ → X → E} {u : X → E} (hf : ∀ j, MemLp (f j) 2 mu) (hu : MemLp u 2 mu)
    (hlim : Tendsto (fun j => ∫ x, ‖f j x - u x‖ ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫ x, ‖f p.1 x - f p.2 x‖ ^ 2 ∂mu)
      (atTop ×ˢ atTop) (𝓝 0) := by
  have h := l2_tendsto_of_integral_sq hf hu hlim
  have hh := ((h.comp tendsto_fst).sub (h.comp tendsto_snd)).norm.pow 2
  simpa only [Function.comp_apply, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), l2_sq_sub] using hh

set_option maxHeartbeats 800000 in




theorem m64Curve_continuous_trace_of_l2_approximation
    (w d : ℕ → ℝ → E) (hd : ∀ j, Continuous (d j))
    (hw : ∀ j t, HasDerivAt (w j) (d j t) t) {T : ℝ} (hT : 0 < T)
    (u v : ℝ → E) (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hval : Tendsto (fun j => ∫ t in Icc (0 : ℝ) T, ‖w j t - u t‖ ^ 2) atTop (𝓝 0))
    (hder : Tendsto (fun j => ∫ t in Icc (0 : ℝ) T, ‖d j t - v t‖ ^ 2) atTop (𝓝 0)) :
    ∃ W : ℝ → E, ContinuousOn W (Icc (0 : ℝ) T) ∧
      W =ᵐ[volume.restrict (Icc (0 : ℝ) T)] u ∧
      TendstoUniformlyOn w W atTop (Icc (0 : ℝ) T) := by
  have hwc (j : ℕ) : Continuous (w j) :=
    continuous_iff_continuousAt.mpr fun t => (hw j t).continuousAt
  have hwL (j : ℕ) : MemLp (w j) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
    apply (memLp_two_iff_integrable_sq_norm (hwc j).aestronglyMeasurable).mpr
    exact ((hwc j).norm.pow 2).integrableOn_Icc
  have hdL (j : ℕ) : MemLp (d j) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
    apply (memLp_two_iff_integrable_sq_norm (hd j).aestronglyMeasurable).mpr
    exact ((hd j).norm.pow 2).integrableOn_Icc
  have hstrong := l2_tendsto_of_integral_sq hwL hu hval
  have hvc := l2_pair_integral_tendsto hwL hu hval
  have hpc := l2_pair_integral_tendsto hdL hv hder
  have hc := m64Curve_uniformCauchy_of_h1 w d hd hw hT hvc hpc
  obtain ⟨k, hk, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hstrong).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) T), ∀ j,
      (hwL (k j)).toLp (w (k j)) x = w (k j) x :=
    ae_all_iff.mpr fun j => (hwL (k j)).coeFn_toLp
  have hraw : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) T),
      Tendsto (fun j => w (k j) x) atTop (𝓝 (u x)) := by
    filter_upwards [hae, hrep, hu.coeFn_toLp] with x hx hxr hxu
    simpa only [hxr, hxu] using hx
  have hval' : Tendsto (fun p : ℕ × ℕ => ∫ t in Icc (0 : ℝ) T,
      ‖w (k p.1) t - w (k p.2) t‖ ^ 2) (atTop ×ˢ atTop) (𝓝 0) :=
    hvc.comp (hk.tendsto_atTop.prodMap hk.tendsto_atTop)
  have hder' : Tendsto (fun p : ℕ × ℕ => ∫ t in Icc (0 : ℝ) T,
      ‖d (k p.1) t - d (k p.2) t‖ ^ 2) (atTop ×ˢ atTop) (𝓝 0) :=
    hpc.comp (hk.tendsto_atTop.prodMap hk.tendsto_atTop)
  obtain ⟨W, hW, hWu, hsub⟩ := m64Curve_continuous_representative_of_h1
    (fun j => w (k j)) (fun j => d (k j)) (fun j => hd (k j)) (fun j => hw (k j))
    hT hval' hder' u hraw
  refine ⟨W, hW, hWu, hc.tendstoUniformlyOn_of_tendsto ?_⟩
  intro x hx
  have hcx : CauchySeq (fun j => w j x) := hc.cauchy_map hx
  exact tendsto_nhds_of_cauchySeq_of_subseq hcx hk.tendsto_atTop (hsub.tendsto_at hx)

end PoincareConjecture
