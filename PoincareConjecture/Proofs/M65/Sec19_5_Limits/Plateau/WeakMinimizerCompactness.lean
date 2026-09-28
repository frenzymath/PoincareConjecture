import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerLocalization
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.WeakGraphClosure
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.CompactApproximation
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.InteriorCutoff
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Cutoff










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff ENNReal

namespace PoincareConjecture

private theorem m65ZeroExtension_norm_le
    (u : Lp ℝ 2 (volume.restrict loopDiskSet))
    (v : Lp ℝ 2 (volume : Measure LoopPlane)) (f : LoopPlane → ℝ)
    (hv : v =ᵐ[volume] loopDiskSet.indicator f) {C : ℝ}
    (hbound : ∀ᵐ z ∂volume.restrict loopDiskSet, ‖f z‖ ≤ C * ‖u z‖) :
    ‖v‖ ≤ C * ‖u‖ := by
  have hZ : MemLp (loopDiskSet.indicator (u : LoopPlane → ℝ)) 2 volume :=
    (memLp_indicator_iff_restrict
      (show MeasurableSet loopDiskSet from measurableSet_closedBall)).mpr (Lp.memLp u)
  let Z := hZ.toLp (loopDiskSet.indicator (u : LoopPlane → ℝ))
  have hnorm : ‖Z‖ = ‖u‖ := by
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict
      (show MeasurableSet loopDiskSet from measurableSet_closedBall), Lp.norm_def]
  rw [← hnorm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hv, hZ.coeFn_toLp, (ae_restrict_iff'
    (show MeasurableSet loopDiskSet from measurableSet_closedBall)).mp hbound] with z hz hZz hb
  rw [hz, hZz]
  by_cases hs : z ∈ loopDiskSet
  · simpa only [indicator_of_mem hs] using hb hs
  · simp only [indicator_of_notMem hs, norm_zero, mul_zero, le_refl]

private theorem m65WeakCutoff_norm_bounds
    (u : Lp ℝ 2 (volume.restrict loopDiskSet))
    (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
    (θ : 𝓢(LoopPlane, ℝ)) (U : Lp ℝ 2 (volume : Measure LoopPlane))
    (D : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hU : U =ᵐ[volume] loopDiskSet.indicator (fun z => θ z * u z))
    (hD : ∀ i, D i =ᵐ[volume] loopDiskSet.indicator (fun z => θ z * d i z +
      fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * u z))
    (hθ : ∀ z, |θ z| ≤ 1) {B : ℝ}
    (hθD : ∀ i z, |fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ B) :
    ‖U‖ ≤ ‖u‖ ∧ ∀ i, ‖D i‖ ≤ ‖d i‖ + B * ‖u‖ := by
  have hθnorm (z : LoopPlane) : ‖θ z‖ ≤ 1 := hθ z
  have hUnorm := m65ZeroExtension_norm_le u U _ hU (C := 1)
    (ae_of_all _ fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hθnorm z) (norm_nonneg _))
  refine ⟨by simpa only [one_mul] using hUnorm, ?_⟩
  intro i
  let e := EuclideanSpace.basisFun (Fin 2) ℝ i
  have hf : MemLp (fun z => θ z * d i z) 2 (volume.restrict loopDiskSet) :=
    (Lp.memLp (d i)).mul' ((θ.memLp ∞ volume).restrict loopDiskSet)
  have hg : MemLp (fun z => fderiv ℝ θ z e * u z) 2 (volume.restrict loopDiskSet) :=
    (Lp.memLp u).mul' (((∂_{e} θ).memLp ∞ volume).restrict loopDiskSet)
  have hF := (memLp_indicator_iff_restrict
    (show MeasurableSet loopDiskSet from measurableSet_closedBall)).mpr hf
  have hG := (memLp_indicator_iff_restrict
    (show MeasurableSet loopDiskSet from measurableSet_closedBall)).mpr hg
  let F := hF.toLp (loopDiskSet.indicator (fun z => θ z * d i z))
  let G := hG.toLp (loopDiskSet.indicator (fun z => fderiv ℝ θ z e * u z))
  have hsplit : D i = F + G := by
    apply Lp.ext
    filter_upwards [hD i, hF.coeFn_toLp, hG.coeFn_toLp, Lp.coeFn_add F G]
      with z hd hf hg hs
    rw [hd, hs, Pi.add_apply, hf, hg]
    by_cases hz : z ∈ loopDiskSet
    · simp only [indicator_of_mem hz, e]
    · simp only [indicator_of_notMem hz, add_zero]
  have hFnorm := m65ZeroExtension_norm_le (d i) F _ hF.coeFn_toLp (C := 1)
    (ae_of_all _ fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hθnorm z) (norm_nonneg _))
  have hGnorm := m65ZeroExtension_norm_le u G _ hG.coeFn_toLp (C := B)
    (ae_of_all _ fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hθD i z) (norm_nonneg _))
  rw [hsplit]
  simpa only [one_mul] using (norm_add_le F G).trans (add_le_add hFnorm hGnorm)






theorem m65WeakTrace_disk_totallyBounded {I : Type*}
    (u : I → Lp ℝ 2 (volume.restrict loopDiskSet))
    (d : I → Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
    (b : I → Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (htrace : ∀ n, M65DiskWeakTrace (u n) (d n) (b n))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvalue : ∀ n, ∀ᵐ z ∂volume.restrict loopDiskSet, ‖u n z‖ ≤ C)
    (hderiv : ∀ n i, ‖d n i‖ ≤ D) : TotallyBounded (range u) := by
  classical
  let mu : Measure LoopPlane := volume.restrict loopDiskSet
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall (0 : LoopPlane) 1).measure_lt_top.ne
  have hconst : MemLp (fun _ : LoopPlane => C) 2 mu := memLp_const C
  let R : ℝ := ‖hconst.toLp (fun _ => C)‖
  have hR : 0 ≤ R := norm_nonneg _
  have huR (n : I) : ‖u n‖ ≤ R := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hvalue n, hconst.coeFn_toLp] with z hz hc
    simpa only [hc, Real.norm_eq_abs, abs_of_nonneg hC] using hz
  apply Metric.totallyBounded_range_of_uniform_approximation
  intro eps heps
  obtain ⟨theta, hthetaOut, hsmall⟩ :=
    ContDiffBump.exists_integral_sub_one_sq_lt (E := LoopPlane) volume
      (eps := eps ^ 2 / (C ^ 2 + 1)) (by positivity)
  let θ : 𝓢(LoopPlane, ℝ) := theta.hasCompactSupport.toSchwartzMap theta.contDiff
  have hsupport : tsupport θ ⊆ ball (0 : LoopPlane) 1 := by
    change tsupport theta ⊆ _
    rw [theta.tsupport_eq]
    exact closedBall_subset_ball hthetaOut
  have hθ (z : LoopPlane) : |θ z| ≤ 1 := by
    change |theta z| ≤ 1
    rw [abs_of_nonneg theta.nonneg]
    exact theta.le_one
  obtain ⟨B0, hB0⟩ := (theta.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((theta.contDiff : ContDiff ℝ 1 theta).continuous_fderiv one_ne_zero)
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hθD (i : Fin 2) (z : LoopPlane) :
      |fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ B := by
    change ‖fderiv ℝ theta z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ B
    apply ((fderiv ℝ theta z).le_opNorm _).trans
    rw [(EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one]
    exact (hB0 z).trans (le_max_left _ _)
  choose U G hU hG hpair using fun n => m65WeakTrace_cutoff_global (htrace n) θ hsupport
  have hbnd (n : I) := m65WeakCutoff_norm_bounds (u n) (d n) θ (U n) (G n)
    (hU n) (hG n) hθ hθD
  have htbGlobal : TotallyBounded (range U) := by
    apply EuclideanGraphRellichNative.totallyBounded_of_supported_weakDerivatives
      theta.hasCompactSupport (R := R) (D := D + B * R) (by positivity)
    · rintro _ ⟨n, rfl⟩
      exact (hbnd n).1.trans (huR n)
    · rintro _ ⟨n, rfl⟩
      refine ⟨G n, ?_, ?_, ?_⟩
      · intro i
        exact ((hbnd n).2 i).trans
          (add_le_add (hderiv n i) (mul_le_mul_of_nonneg_left (huR n) hB))
      · filter_upwards [hU n] with z hz hnot
        rw [hz]
        by_cases hdisk : z ∈ loopDiskSet
        · rw [indicator_of_mem hdisk]
          change theta z * u n z = 0
          rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]
        · rw [indicator_of_notMem hdisk]
      · intro i test
        have hh := hpair n i test
        rw [DeTurckDomainRegularityNative.inner_schwartz (U n)] at hh
        simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
          EuclideanSpace.basisFun_apply] using hh
  let restrict := LpToLpRestrictCLM LoopPlane ℝ ℝ volume 2 loopDiskSet
  let v (n : I) := restrict (U n)
  have htb : TotallyBounded (range v) := by
    simpa only [← range_comp, Function.comp_def, v] using
      htbGlobal.image restrict.uniformContinuous
  refine ⟨v, htb, ?_⟩
  intro n
  have hv : v n =ᵐ[mu] fun z => θ z * u n z := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ loopDiskSet (U n),
      ae_restrict_of_ae (hU n), ae_restrict_mem measurableSet_closedBall] with z hz hu hdisk
    rw [hz, hu, indicator_of_mem hdisk]
  have hθmeas : AEStronglyMeasurable θ mu := θ.continuous.aestronglyMeasurable
  have hθAE : ∀ᵐ z ∂mu, |θ z| ≤ 1 := ae_of_all _ hθ
  have hvcut : v n = ((Lp.memLp (u n)).smul_cutoff hθmeas hθAE).toLp
      (fun z => θ z • u n z) := by
    apply Lp.ext
    exact hv.trans ((Lp.memLp (u n)).smul_cutoff hθmeas hθAE).coeFn_toLp.symm
  have herr := Lp.norm_sub_cutoff_sq_le (u n) hθmeas hθAE hC (hvalue n)
  rw [← hvcut] at herr
  have hnonneg : 0 ≤ ∫ z in loopDiskSet, (1 - θ z) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsmall' := (lt_div_iff₀ (show 0 < C ^ 2 + 1 by positivity)).mp hsmall
  rw [dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) heps.le).mp
  change ‖u n - v n‖ ^ 2 ≤ C ^ 2 * ∫ z in loopDiskSet, (1 - θ z) ^ 2 at herr
  change (∫ z in loopDiskSet, (1 - θ z) ^ 2) * (C ^ 2 + 1) < eps ^ 2 at hsmall'
  nlinarith

end PoincareConjecture
