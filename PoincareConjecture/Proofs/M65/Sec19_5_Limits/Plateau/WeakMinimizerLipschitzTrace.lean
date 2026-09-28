import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerTrace
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.LipschitzWeakDerivative
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Restriction
import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff NNReal
  BoundedContinuousFunction

namespace PoincareConjecture

open EuclideanTranslationNative EuclideanMollificationNative DeTurckDomainRegularityNative

theorem m65Mollify_lipschitz_error {f : LoopPlane → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hfL2 : MemLp f 2 volume) {ε : ℝ} (hε : 0 < ε)
    (x : LoopPlane) : |mollify hε (hfL2.toLp f) x - f x| ≤ C * ε := by
  rw [mollify_sub_eq_integral hε hf.continuous hfL2 x]
  have hi : Integrable (fun y => mollifier hε y * |f (x - y) - f x|) volume :=
    integrable_mollifier_mul_continuous hε
      ((hf.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const).abs
  calc
    |∫ y, mollifier hε y * (f (x - y) - f x)| ≤
        ∫ y, mollifier hε y * |f (x - y) - f x| := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg hε _)] using
        norm_integral_le_integral_norm (fun y => mollifier hε y * (f (x - y) - f x))
    _ ≤ ∫ y : LoopPlane, mollifier hε y * (C * ε) := by
      apply integral_mono hi ((mollifier_integrable hε).mul_const _)
      intro y
      by_cases hy : mollifier hε y = 0
      · simp only [hy, zero_mul, le_refl]
      · apply mul_le_mul_of_nonneg_left _ (mollifier_nonneg hε y)
        have hbound : |f (x - y) - f x| ≤ C * ‖y‖ := by
          simpa only [dist_eq_norm, Real.norm_eq_abs, sub_sub_cancel_left, norm_neg] using
            hf.dist_le_mul (x - y) x
        exact hbound.trans (mul_le_mul_of_nonneg_left
          (norm_le_of_mollifier_ne_zero hε hy) C.coe_nonneg)
    _ = C * ε := by rw [integral_mul_const, mollifier_integral, one_mul]

private theorem m65CompactLip_derivative_memLp {f : LoopPlane → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hs : HasCompactSupport f) (i : Fin 2) :
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 volume := by
  apply (hs.fderiv_apply ℝ _).memLp_of_bound
    (measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable (C : ℝ)
  apply ae_of_all
  intro x
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [(EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hf)

private theorem m65Lipschitz_mollify_boundary_limit
    {f : LoopPlane → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hs : HasCompactSupport f) (hfL2 : MemLp f 2 volume)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (S : ℕ → 𝓢(LoopPlane, ℝ))
    (hS : ∀ n x, S n x = mollify (hε n) (hfL2.toLp f) x)
    (hbL2 : MemLp (fun θ => f (Proofs.M58.angularPoint θ)) 2
      (volume.restrict (Icc (-Real.pi) Real.pi))) :
    ∃ b : ℕ → Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi)),
      (∀ n, b n =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
        fun θ => S n (Proofs.M58.angularPoint θ)) ∧
      Tendsto b atTop (𝓝 (hbL2.toLp (fun θ => f (Proofs.M58.angularPoint θ)))) := by
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hf.continuous
  let fB : LoopPlane →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous B hB
  have hconv : Tendsto (fun n => (S n).toBoundedContinuousFunction) atTop (𝓝 fB) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
    · intro n
      apply (BoundedContinuousFunction.norm_le (mul_nonneg C.coe_nonneg (hε n).le)).mpr
      intro x
      change |S n x - f x| ≤ _
      rw [hS]
      exact m65Mollify_lipschitz_error hf hfL2 (hε n) x
    · simpa only [mul_zero] using (tendsto_const_nhds (x := (C : ℝ))).mul hε0
  let circle : C(ℝ, LoopPlane) :=
    ⟨Proofs.M58.angularPoint, Proofs.M58.contDiff_angularPoint.continuous⟩
  let mu : Measure ℝ := volume.restrict (Icc (-Real.pi) Real.pi)
  let b (n : ℕ) : Lp ℝ 2 mu := BoundedContinuousFunction.toLp 2 mu ℝ
    ((S n).toBoundedContinuousFunction.compContinuous circle)
  have hlim := ((BoundedContinuousFunction.toLp 2 mu ℝ).continuous.tendsto
    (fB.compContinuous circle)).comp
      ((BoundedContinuousFunction.continuous_compContinuous circle).tendsto fB |>.comp hconv)
  have heq : BoundedContinuousFunction.toLp 2 mu ℝ (fB.compContinuous circle) =
      hbL2.toLp (fun θ => f (Proofs.M58.angularPoint θ)) := by
    apply Lp.ext
    exact (BoundedContinuousFunction.coeFn_toLp 2 mu ℝ (fB.compContinuous circle)).trans
      hbL2.coeFn_toLp.symm
  refine ⟨b, ?_, ?_⟩
  · intro n
    exact BoundedContinuousFunction.coeFn_toLp 2 mu ℝ _
  · rw [heq] at hlim
    exact hlim

theorem m65CompactLipschitz_diskWeakTrace {f : LoopPlane → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hs : HasCompactSupport f) :
    ∃ (u : Lp ℝ 2 (volume.restrict loopDiskSet))
      (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
      (b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))),
      u =ᵐ[volume.restrict loopDiskSet] f ∧
      (∀ i, d i =ᵐ[volume.restrict loopDiskSet]
        fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ∧
      b =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
        (fun θ => f (Proofs.M58.angularPoint θ)) ∧ M65DiskWeakTrace u d b := by
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  have hfL2 : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hs
  have hdL2 (i : Fin 2) : MemLp (fun x => fderiv ℝ f x (B i)) 2 volume :=
    m65CompactLip_derivative_memLp hf hs i
  have hbL2 : MemLp (fun θ => f (Proofs.M58.angularPoint θ)) 2
      (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    have hc := hf.continuous.comp Proofs.M58.contDiff_angularPoint.continuous
    exact (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
      ((hc.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  let ug : ScalarL2 2 := hfL2.toLp f
  let dg (i : Fin 2) : ScalarL2 2 := (hdL2 i).toLp (fun x => fderiv ℝ f x (B i))
  have huK : ∀ᵐ x ∂volume, x ∉ tsupport f → ug x = 0 := by
    filter_upwards [hfL2.coeFn_toLp] with x hx hxs
    exact hx.trans (image_eq_zero_of_notMem_tsupport hxs)
  have hweak (i : Fin 2) (test : 𝓢(LoopPlane, ℝ)) :
      ⟪dg i, test.toLp 2 volume⟫_ℝ =
        -(∫ x, ug x * fderiv ℝ test x (B i)) :=
    hf.inner_toLp_fderiv_schwartz hs hfL2 (B i) (hdL2 i) test
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let S : ℕ → 𝓢(LoopPlane, ℝ) := fun n => mollifySchwartz (hε n) ug hs huK
  have hS (n : ℕ) (x : LoopPlane) : S n x = mollify (hε n) ug x := rfl
  have hvg : Tendsto (fun n => (S n).toLp 2 volume) atTop (𝓝 ug) := by
    simpa only [S, mollifySchwartz_toLp] using tendsto_mollifyL2 ε hε hε0 ug
  have hdg (i : Fin 2) :
      Tendsto (fun n => (∂_{B i} (S n)).toLp 2 volume) atTop (𝓝 (dg i)) := by
    have heq (n : ℕ) : (∂_{B i} (S n)).toLp 2 volume = mollifyL2 (hε n) (dg i) :=
      lineDeriv_mollifySchwartz_toLp (hε n) ug (dg i) hs huK (B i) (hweak i)
    simp only [heq]
    exact tendsto_mollifyL2 ε hε hε0 (dg i)
  let u : Lp ℝ 2 (volume.restrict loopDiskSet) := (hfL2.restrict loopDiskSet).toLp f
  let d (i : Fin 2) : Lp ℝ 2 (volume.restrict loopDiskSet) :=
    ((hdL2 i).restrict loopDiskSet).toLp (fun x => fderiv ℝ f x (B i))
  let b := hbL2.toLp (fun θ => f (Proofs.M58.angularPoint θ))
  obtain ⟨bn, hbn, hbconv⟩ := m65Lipschitz_mollify_boundary_limit hf hs hfL2 hε hε0 S hS hbL2
  have huconv : Tendsto (fun n => m65DiskTestL2 (S n)) atTop (𝓝 u) := by
    have h := ((LpToLpRestrictCLM LoopPlane ℝ ℝ volume 2 loopDiskSet).continuous.tendsto
      ug).comp hvg
    simpa only [Function.comp_def, SchwartzMap.toLp, LpToLpRestrictCLM_toLp,
      ug, u, m65DiskTestL2] using h
  have hdconv (i : Fin 2) :
      Tendsto (fun n => m65DiskTestL2 (∂_{B i} (S n))) atTop (𝓝 (d i)) := by
    have h := ((LpToLpRestrictCLM LoopPlane ℝ ℝ volume 2 loopDiskSet).continuous.tendsto
      (dg i)).comp (hdg i)
    simpa only [Function.comp_def, SchwartzMap.toLp, LpToLpRestrictCLM_toLp,
      dg, d, m65DiskTestL2] using h
  have htrace (n : ℕ) : M65DiskWeakTrace (m65DiskTestL2 (S n))
      (fun i => m65DiskTestL2 (∂_{B i} (S n))) (bn n) := by
    have hbS : MemLp (fun θ => S n (Proofs.M58.angularPoint θ)) 2
        (volume.restrict (Icc (-Real.pi) Real.pi)) := by
      have hc := (S n).continuous.comp Proofs.M58.contDiff_angularPoint.continuous
      exact (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
        ((hc.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    have heq : bn n = hbS.toLp (fun θ => S n (Proofs.M58.angularPoint θ)) :=
      Lp.ext ((hbn n).trans hbS.coeFn_toLp.symm)
    rw [heq]
    exact m65DiskWeakTrace_of_C1 (S n) ((S n).smooth 1)
      (((S n).memLp 2 volume).restrict loopDiskSet)
      (fun i => ((∂_{B i} (S n)).memLp 2 volume).restrict loopDiskSet) hbS
  refine ⟨u, d, b, (hfL2.restrict loopDiskSet).coeFn_toLp,
    fun i => ((hdL2 i).restrict loopDiskSet).coeFn_toLp, hbL2.coeFn_toLp, ?_⟩
  exact m65DiskWeakTrace_of_limit htrace huconv
    (fun i v => (hdconv i).inner tendsto_const_nhds) hbconv

private theorem m65DiskLip_compact_extension {f : LoopPlane → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f loopDiskSet) :
    ∃ (g : LoopPlane → ℝ) (K : ℝ≥0),
      LipschitzWith K g ∧ HasCompactSupport g ∧ EqOn f g loopDiskSet := by
  obtain ⟨F, hF, hext⟩ := hf.extend_real
  let R : ℝ := ‖f 0‖ + C + 1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hfbound (x : LoopPlane) (hx : x ∈ loopDiskSet) : |f x| ≤ R := by
    have hz : (0 : LoopPlane) ∈ loopDiskSet := mem_closedBall_self (by norm_num)
    have hdiff : |f x - f 0| ≤ C * ‖x‖ := by
      simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hf.dist_le_mul x hx 0 hz
    have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hnorm := norm_le_norm_sub_add (f x) (f 0)
    simp only [Real.norm_eq_abs] at hnorm
    have hmul := mul_le_mul_of_nonneg_left hxnorm C.coe_nonneg
    dsimp only [R]
    rw [Real.norm_eq_abs]
    nlinarith
  let H := fun x : LoopPlane => min (max (F x) (-R)) R
  have hH : LipschitzWith C H := (hF.max_const (-R)).min_const R
  have hHbound (x : LoopPlane) : |H x| ≤ R := by
    apply abs_le.mpr
    exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩
  have hHeq (x : LoopPlane) (hx : x ∈ loopDiskSet) : H x = f x := by
    dsimp only [H]
    rw [← hext hx, max_eq_left (abs_le.mp (hfbound x hx)).1,
      min_eq_left (abs_le.mp (hfbound x hx)).2]
  let χ := fun x : LoopPlane => min (max (2 - ‖x‖) 0) 1
  have hraw : LipschitzWith 1 (fun x : LoopPlane => 2 - ‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (2 - ‖x‖) (2 - ‖y‖) = |‖y‖ - ‖x‖| := by rw [Real.dist_eq]; congr 1; ring
      _ = dist ‖x‖ ‖y‖ := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ _ := lipschitzWith_one_norm.dist_le_mul x y
  have hχ : LipschitzWith 1 χ := (hraw.max_const 0).min_const 1
  have hχbound (x : LoopPlane) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (le_min (le_max_right _ _) zero_le_one)]
    exact min_le_right _ _
  have hχeq (x : LoopPlane) (hx : x ∈ loopDiskSet) : χ x = 1 := by
    have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    dsimp only [χ]
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  let g := fun x => χ x * H x
  have hg : LipschitzWith (C + ⟨R, hR⟩) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hHdiff : |H x - H y| ≤ C * dist x y := by
      simpa only [Real.dist_eq] using hH.dist_le_mul x y
    have hχdiff : |χ x - χ y| ≤ dist x y := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hχ.dist_le_mul x y
    change |χ x * H x - χ y * H y| ≤ (C + R) * dist x y
    calc
      _ = |χ x * (H x - H y) + (χ x - χ y) * H y| := by congr 1; ring
      _ ≤ |χ x| * |H x - H y| + |χ x - χ y| * |H y| := by
        simpa only [abs_mul] using abs_add_le (χ x * (H x - H y)) ((χ x - χ y) * H y)
      _ ≤ 1 * (C * dist x y) + dist x y * R :=
        add_le_add
          (mul_le_mul (hχbound x) hHdiff (abs_nonneg _) (by norm_num))
          (mul_le_mul hχdiff (hHbound y) (abs_nonneg _) (dist_nonneg))
      _ = _ := by ring
  have hs : HasCompactSupport g := by
    apply (isCompact_closedBall (0 : LoopPlane) 2).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hxball
    have hxnorm : 2 < ‖x‖ := lt_of_not_ge (fun h => hxball (mem_closedBall_zero_iff.mpr h))
    have hzero : χ x = 0 := by
      dsimp only [χ]
      rw [max_eq_right (by linarith), min_eq_left zero_le_one]
    exact hx (by simp only [g, hzero, zero_mul])
  refine ⟨g, C + ⟨R, hR⟩, hg, hs, ?_⟩
  intro x hx
  dsimp only [g]
  rw [hχeq x hx, hHeq x hx, one_mul]

theorem m65LipschitzOn_diskWeakTrace {f : LoopPlane → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f loopDiskSet) :
    ∃ (u : Lp ℝ 2 (volume.restrict loopDiskSet))
      (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
      (b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))),
      u =ᵐ[volume.restrict loopDiskSet] f ∧
      (∀ i, d i =ᵐ[volume.restrict loopDiskSet]
        fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ∧
      b =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
        (fun θ => f (Proofs.M58.angularPoint θ)) ∧ M65DiskWeakTrace u d b := by
  obtain ⟨g, K, hg, hs, hext⟩ := m65DiskLip_compact_extension hf
  obtain ⟨u, d, b, hu, hd, hb, htrace⟩ := m65CompactLipschitz_diskWeakTrace hg hs
  have hball : ∀ᵐ x ∂volume.restrict loopDiskSet, x ∈ ball (0 : LoopPlane) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp
        (Measure.addHaar_sphere_of_ne_zero volume (0 : LoopPlane) one_ne_zero))] with x hx hxs
    change dist x 0 ≤ 1 at hx
    rw [mem_sphere] at hxs
    exact hx.lt_of_ne hxs
  refine ⟨u, d, b, ?_, ?_, ?_, htrace⟩
  · filter_upwards [hu, ae_restrict_mem measurableSet_closedBall] with x hx hxdisk
    exact hx.trans (hext hxdisk).symm
  · intro i
    filter_upwards [hd i, hball] with x hx hxi
    have heq : f =ᶠ[𝓝 x] g := by
      filter_upwards [isOpen_ball.mem_nhds hxi] with y hy
      exact hext (ball_subset_closedBall hy)
    exact hx.trans (congrArg (fun A : LoopPlane →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin 2) ℝ i)) heq.fderiv_eq.symm)
  · filter_upwards [hb] with θ hθ
    exact hθ.trans (hext (mem_closedBall_zero_iff.mpr (Proofs.M58.norm_angularPoint θ).le)).symm

end PoincareConjecture
