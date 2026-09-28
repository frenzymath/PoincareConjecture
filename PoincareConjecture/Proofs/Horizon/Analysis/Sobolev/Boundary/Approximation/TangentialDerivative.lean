import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Approximation.Closure
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Approximation.DifferenceQuotient
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Approximation.TangentialExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Approximation







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryTangential

open Weak Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem uniform_bound {F : Type*} [NormedAddCommGroup F]
    {a : E → F} (ha : Continuous a) (hc : HasCompactSupport a) :
    ∃ C ≥ 0, ∀ x, ‖a x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous ha
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

omit [NeZero d] in
private theorem memLp_mul_compact {μ : Measure E} {a f : E → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a) (hf : MemLp f 2 μ) :
    MemLp (fun x => a x * f x) 2 μ := by
  obtain ⟨C, _, hC⟩ := uniform_bound ha hc
  apply hf.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hf.1)
  exact Eventually.of_forall fun x => by
    simpa only [Pi.mul_apply, norm_mul] using
      mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (f x))

omit [NeZero d] in
private theorem localized_convergence {a : E → ℝ} (ha : Continuous a)
    (hc : HasCompactSupport a) {V O : Set E} (hV : MeasurableSet V)
    (hs : tsupport a ⊆ V) {f : ℕ → E → ℝ}
    (hf : Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a x * f n x) 2 (volume.restrict O))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := uniform_bound ha hc
  have hb (n : ℕ) : eLpNorm (fun x => a x * f n x) 2 (volume.restrict O) ≤
      ENNReal.ofReal C * eLpNorm (f n) 2 (volume.restrict V) := by
    have heq : (fun x => a x * f n x) = V.indicator (fun x => a x * f n x) := by
      funext x
      by_cases hx : x ∈ V
      · simp [hx]
      · have ha0 : a x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
        simp [hx, ha0]
    calc
      _ ≤ eLpNorm (fun x => a x * f n x) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (V.indicator (fun x => a x * f n x)) 2 volume :=
        congrArg (fun f : E → ℝ => eLpNorm f 2 volume) heq
      _ = eLpNorm (fun x => a x * f n x) 2 (volume.restrict V) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hV
      _ ≤ _ := by
        apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul _ 2
        exact Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.const_mul hf (Or.inr ENNReal.ofReal_ne_top))
    (fun _ => bot_le) hb

private theorem diffQuot_indicator_eq (f : E → ℝ) (k : Fin d) (hk : k ≠ 0)
    (h : ℝ) {x : E} (hx : x ∈ halfSpace d) :
    diffQuot k h ((halfSpace d).indicator f) x = diffQuot k h f x := by
  have hx' : x + h • EuclideanSpace.single k 1 ∈ halfSpace d := by
    simpa [halfSpace, PiLp.add_apply, PiLp.smul_apply, hk.symm] using hx
  simp [diffQuot, hx, hx']

omit [NeZero d] in
private theorem memLp_diffQuot_global {f : E → ℝ} (hf : MemLp f 2 volume)
    (k : Fin d) (h : ℝ) : MemLp (diffQuot k h f) 2 volume := by
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h]
    exact MemLp.zero
  · rw [diffQuot_eq_translate_sub_div k hh]
    simpa only [div_eq_mul_inv, Pi.sub_apply] using
      ((memLp_translate k h hf).sub hf).mul_const h⁻¹

private theorem weakPartial_diffQuot_halfSpace {u g : E → ℝ}
    (hu : MemLp ((halfSpace d).indicator u) 2 volume)
    (hg : MemLp ((halfSpace d).indicator g) 2 volume)
    (i k : Fin d) (hk : k ≠ 0) (h : ℝ)
    (hw : HasWeakPartialDeriv i ((halfSpace d).indicator g)
      ((halfSpace d).indicator u) univ) :
    HasWeakPartialDeriv i (diffQuot k h ((halfSpace d).indicator g))
      (diffQuot k h u) (halfSpace d) := by
  have ht := (NirenbergDiffQuotTestFunction.hasWeakPartialDeriv_diffQuot k i h
    (by simpa using hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (by simpa using hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hw).restrict
      isOpen_halfSpace (subset_univ _)
  intro φ hφ hc hs
  calc
    _ = ∫ x in halfSpace d,
        diffQuot k h ((halfSpace d).indicator u) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
      rw [diffQuot_indicator_eq u k hk h hx]
    _ = _ := ht φ hφ hc hs



theorem memW01p_mul_chosenWeakPartial_tangential
    {u χ : E → ℝ} (hu0 : MemW01p 2 u (halfSpace d))
    (hu2 : MemWkp 2 2 u (halfSpace d))
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (k : Fin d) (hk : k ≠ 0) :
    MemW01p 2 (fun x => χ x * chosenWeakPartial' 2 k u (halfSpace d) x)
      (halfSpace d) := by
  classical
  let H := halfSpace d
  let p (i : Fin d) := chosenWeakPartial' 2 i u H
  let q (i : Fin d) := chosenWeakPartial' 2 k (p i) H
  have hp (i : Fin d) : MemLp (p i) 2 (volume.restrict H) :=
    chosenWeakPartial'_memLp_of_mem hu2.memW1p i
  have hpi (i : Fin d) : MemW1p 2 (p i) H := (hu2.chosenWeakPartial_mem i).memW1p
  have hq (i : Fin d) : MemLp (q i) 2 (volume.restrict H) :=
    chosenWeakPartial'_memLp_of_mem (hpi i) k
  have hwp (i : Fin d) : HasWeakPartialDeriv i (p i) u H :=
    chosenWeakPartial'_isWeakPartial_of_mem hu2.memW1p i
  have hwq (i : Fin d) : HasWeakPartialDeriv k (q i) (p i) H :=
    chosenWeakPartial'_isWeakPartial_of_mem (hpi i) k
  let U := H.indicator u
  let P (i : Fin d) := H.indicator (p i)
  let Q (i : Fin d) := H.indicator (q i)
  have hU : MemLp U 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu2.memLp
  have hP (i : Fin d) : MemLp (P i) 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hp i)
  have hQ (i : Fin d) : MemLp (Q i) 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hq i)
  let wu : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) u H :=
    { memLp := by simpa using hu2.memLp
      weakGrad := fun x => WithLp.toLp 2 (fun i => p i x)
      weakGrad_component_memLp := fun i => by simpa using hp i
      isWeakGrad := hwp }
  have hzero (i : Fin d) : HasWeakPartialDeriv i (P i) U univ := by
    have hz := (zeroExtendMemW1pWitnessP (p := 2) isOpen_halfSpace (by norm_num)
      (by simpa using hu0) wu).isWeakGrad i
    simpa [zeroExtendMemW1pWitnessP, wu, P, U, H, PiLp.toLp_apply] using hz
  have hzeroP (i : Fin d) : HasWeakPartialDeriv k (Q i) (P i) univ :=
    hasWeakPartialDeriv_indicator_halfSpace k hk (hp i) (hq i) (hwq i)
  let step (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hstep : Tendsto step atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun n => by
      change 1 / ((n : ℝ) + 1) ≠ 0
      positivity
  obtain ⟨R, _, hsR⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  let V : Set E := Metric.ball 0 (R + 1)
  have hV : IsOpen V := Metric.isOpen_ball
  have hVc : IsCompact (closure V) :=
    (isCompact_closedBall (0 : E) (R + 1)).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  have hsV : tsupport χ ⊆ V := hsR.trans (Metric.closedBall_subset_ball (by linarith))
  let D (i : Fin d) (x : E) := fderiv ℝ χ x (EuclideanSpace.single i 1)
  have hD (i : Fin d) : Continuous (D i) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc (i : Fin d) : HasCompactSupport (D i) := hc.fderiv_apply ℝ _
  have hDs (i : Fin d) : tsupport (D i) ⊆ V :=
    (tsupport_fderiv_apply_subset ℝ _).trans hsV
  obtain ⟨C₀, hC₀, hCχ⟩ := uniform_bound hχ.continuous hc
  obtain ⟨C₁, hC₁, hCDχ⟩ := uniform_bound (hχ.continuous_fderiv (by simp)) (hc.fderiv ℝ)
  let wdq (h : ℝ) : MemW1pWitness 2 (diffQuot k h u) H :=
    { memLp := (memW01p_diffQuot hu0 k hk h).1.1
      weakGrad := fun x => WithLp.toLp 2 (fun i => diffQuot k h (P i) x)
      weakGrad_component_memLp := fun i => (memLp_diffQuot_global (hP i) k h).restrict H
      isWeakGrad := fun i => weakPartial_diffQuot_halfSpace hU (hP i) i k hk h (hzero i) }
  let wseq (n : ℕ) : MemW1pWitness 2 (fun x => χ x * diffQuot k (step n) u x) H :=
    (wdq (step n)).mulSmoothBoundedP (by norm_num) isOpen_halfSpace hχ hC₀ hC₁
      (by simpa only [Real.norm_eq_abs] using hCχ) hCDχ
  have hseq (n : ℕ) : MemW01p 2 (fun x => χ x * diffQuot k (step n) u x) H :=
    memW01p_mul_smooth isOpen_halfSpace (memW01p_diffQuot hu0 k hk (step n)) hχ hc
  have hlimU : Tendsto (fun n => eLpNorm
      (fun x => diffQuot k (step n) U x - P k x) 2 (volume.restrict V)) atTop (𝓝 0) :=
    (BoundaryApproximation.tendsto_eLpNorm_diffQuot_sub_weakPartial hU (hP k) k
      (hzero k) hV hVc).comp hstep
  have hlimP (i : Fin d) : Tendsto (fun n => eLpNorm
      (fun x => diffQuot k (step n) (P i) x - Q i x) 2 (volume.restrict V)) atTop (𝓝 0) :=
    (BoundaryApproximation.tendsto_eLpNorm_diffQuot_sub_weakPartial (hP i) (hQ i) k
      (hzeroP i) hV hVc).comp hstep
  let target : E → ℝ := fun x => χ x * p k x
  let G (i : Fin d) (x : E) := χ x * Q i x + D i x * P k x
  have htarget : MemLp target 2 (volume.restrict H) := memLp_mul_compact hχ.continuous hc (hp k)
  have hG (i : Fin d) : MemLp (G i) 2 (volume.restrict H) :=
    ((memLp_mul_compact hχ.continuous hc (hQ i)).add
      (memLp_mul_compact (hD i) (hDc i) (hP k))).restrict H
  have hv : Tendsto (fun n => eLpNorm
      (fun x => χ x * diffQuot k (step n) u x - target x) 2 (volume.restrict H))
      atTop (𝓝 0) := by
    have hl := localized_convergence (O := H) hχ.continuous hc hV.measurableSet hsV hlimU
    apply hl.congr'
    refine Eventually.of_forall fun n => eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
    change χ x * (diffQuot k (step n) U x - P k x) =
      χ x * diffQuot k (step n) u x - χ x * p k x
    rw [diffQuot_indicator_eq u k hk (step n) hx, show P k x = p k x from
      Set.indicator_of_mem hx _]
    ring
  have hd (i : Fin d) : Tendsto (fun n => eLpNorm
      (fun x => (wseq n).weakGrad x i - G i x) 2 (volume.restrict H)) atTop (𝓝 0) := by
    have hl1 := localized_convergence (O := H) hχ.continuous hc hV.measurableSet hsV (hlimP i)
    have hl2 := localized_convergence (O := H) (hD i) (hDc i) hV.measurableSet (hDs i) hlimU
    have hb (n : ℕ) : eLpNorm (fun x => (wseq n).weakGrad x i - G i x) 2
        (volume.restrict H) ≤
        eLpNorm (fun x => χ x * (diffQuot k (step n) (P i) x - Q i x)) 2 (volume.restrict H) +
        eLpNorm (fun x => D i x * (diffQuot k (step n) U x - P k x)) 2 (volume.restrict H) := by
      have heq : (fun x => (wseq n).weakGrad x i - G i x) =ᵐ[volume.restrict H]
          (fun x => χ x * (diffQuot k (step n) (P i) x - Q i x) +
            D i x * (diffQuot k (step n) U x - P k x)) := by
        filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
        simp only [wseq, wdq, MemW1pWitness.mulSmoothBoundedP, PiLp.add_apply,
          PiLp.smul_apply, smul_eq_mul, G, D]
        rw [diffQuot_indicator_eq u k hk (step n) hx]
        ring
      rw [eLpNorm_congr_ae heq]
      apply eLpNorm_add_le _ _ (by norm_num)
      · exact (memLp_mul_compact hχ.continuous hc
          ((memLp_diffQuot_global (hP i) k (step n)).sub (hQ i))).1.restrict
      · exact (memLp_mul_compact (hD i) (hDc i)
          ((memLp_diffQuot_global hU k (step n)).sub (hP k))).1.restrict
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hl1.add hl2) (fun _ => bot_le) hb
  have hwG (i : Fin d) : HasWeakPartialDeriv i (G i) target H := by
    apply HasWeakPartialDeriv.of_eLpNormApprox_p (p := 2) isOpen_halfSpace (by norm_num)
      (by simpa using htarget) (by simpa using hG i)
      (ψ := fun n x => χ x * diffQuot k (step n) u x)
      (gψ := fun n x => (wseq n).weakGrad x i)
    · exact fun n => (wseq n).isWeakGrad i
    · intro n
      convert! (wseq n).memLp.sub htarget using 1
      norm_num
    · simpa using hv
    · intro n
      convert! ((wseq n).weakGrad_component_memLp i).sub (hG i) using 1
      norm_num
    · simpa using hd i
  let w : MemW1pWitness 2 target H :=
    { memLp := htarget
      weakGrad := fun x => WithLp.toLp 2 (fun i => G i x)
      weakGrad_component_memLp := hG
      isWeakGrad := hwG }
  exact MemW01p.of_tendsto_eLpNorm isOpen_halfSpace hseq wseq w hv hd

end Poincare.Analysis.Sobolev.BoundaryTangential
