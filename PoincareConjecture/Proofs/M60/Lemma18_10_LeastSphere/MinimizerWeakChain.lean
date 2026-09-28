import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakChainLimit
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerVectorMollification










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)



theorem suContinuous_memLp_ball {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {a : Plane} {r : ℝ} {p : ℝ≥0∞}
    (hf : ContinuousOn f (Metric.closedBall a r)) :
    MemLp f p (volume.restrict (Metric.ball a r)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball a r) < ⊤)⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hf
  apply (memLp_const C).of_le
    ((hf.mono Metric.ball_subset_closedBall).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact (hC x (Metric.ball_subset_closedBall hx)).trans (le_abs_self C)



theorem suQuadraticDerivative_value_bound {m : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → ℝ} (hF : ContDiff ℝ 1 F)
    {C : ℝ} (hC : 0 < C)
    (hDF : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖ ^ 2)) (y : EuclideanSpace ℝ (Fin m)) :
    ‖F y‖ ≤ (C + ‖F 0‖ + 1) * (1 + ‖y‖ ^ 4) := by
  have hc := convex_closedBall (0 : EuclideanSpace ℝ (Fin m)) ‖y‖
  have h := hc.norm_image_sub_le_of_norm_fderiv_le
      (x := 0) (y := y) (C := C * (1 + ‖y‖ ^ 2))
      (fun x _ => hF.differentiable (by norm_num) x)
      (fun x hx => (hDF x).trans (mul_le_mul_of_nonneg_left (by
        have hx' : ‖x‖ ≤ ‖y‖ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
        nlinarith [norm_nonneg x, norm_nonneg y]) hC.le))
      (Metric.mem_closedBall.mpr (by simp))
      (Metric.mem_closedBall.mpr (by simp))
  simp only [sub_zero] at h
  have hp : ‖y‖ + ‖y‖ ^ 3 ≤ 1 + ‖y‖ ^ 4 := by
    nlinarith only [mul_nonneg (sq_nonneg (‖y‖ - 1))
      (by positivity : 0 ≤ ‖y‖ ^ 2 + ‖y‖ + 1)]
  have hn : ‖F y‖ ≤ ‖F y - F 0‖ + ‖F 0‖ := by
    simpa only [sub_add_cancel] using norm_add_le (F y - F 0) (F 0)
  nlinarith [mul_nonneg (norm_nonneg (F 0)) (pow_nonneg (norm_nonneg y) 4),
    mul_le_mul_of_nonneg_left hp hC.le]

private theorem restrict_limit {m : ℕ} {p : ℝ≥0∞} {O : Set Plane}
    (hO : MeasurableSet O) {v : ℕ → Plane → EuclideanSpace ℝ (Fin m)}
    {u U : Plane → EuclideanSpace ℝ (Fin m)} (he : EqOn U u O)
    (hlim : Tendsto (fun j => eLpNorm (v j - U) p volume) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (v j - u) p (volume.restrict O)) atTop (𝓝 0) := by
  have hb (j : ℕ) : eLpNorm (v j - u) p (volume.restrict O) ≤
      eLpNorm (v j - U) p volume := by
    calc
      _ = eLpNorm (v j - U) p (volume.restrict O) := eLpNorm_congr_ae (by
        filter_upwards [ae_restrict_mem hO] with x hx
        simp only [Pi.sub_apply, he hx])
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hb





theorem suWeakPartial_comp_quadratic {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {W : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {a : Plane} {R r : ℝ}
    (_hr : 0 < r) (hrR : r < R)
    (hu : MemLp u 4 (volume.restrict (Metric.ball a R)))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (Metric.ball a R)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun x => W i x b) (fun x => u x b)
      (Metric.ball a R))
    {F : EuclideanSpace ℝ (Fin m) → ℝ} (hF : ContDiff ℝ 1 F)
    {C : ℝ} (hC : 0 < C) (hDF : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖ ^ 2))
    (i : Fin 2) :
    HasWeakPartialDeriv i (fun x => fderiv ℝ F (u x) (W i x))
      (fun x => F (u x)) (Metric.ball a r) := by
  let O : Set Plane := Metric.ball a R
  let I : Set Plane := Metric.ball a r
  let U : Plane → EuclideanSpace ℝ (Fin m) := O.indicator u
  let Q : Plane → EuclideanSpace ℝ (Fin m) := O.indicator (W i)
  have hU : MemLp U 4 volume :=
    (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet).mpr hu
  have hQ : MemLp Q 2 volume :=
    (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet).mpr (hW i)
  have hUl : LocallyIntegrable U volume := hU.locallyIntegrable (by norm_num)
  have hQl : LocallyIntegrable Q volume := hQ.locallyIntegrable (by norm_num)
  let ε : ℕ → ℝ := fun j => ((R - r) / 4) * (1 / 2 : ℝ) ^ j
  have hε (j : ℕ) : 0 < ε j :=
    mul_pos (div_pos (sub_pos.mpr hrR) (by norm_num)) (pow_pos (by norm_num) _)
  have hεb (j : ℕ) : ε j ≤ (R - r) / 4 :=
    mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hεz : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((R - r) / 4)
  let v : ℕ → Plane → EuclideanSpace ℝ (Fin m) := fun j =>
    mollifierEps (hε j) ⋆[lsmul ℝ ℝ, volume] U
  let q : ℕ → Plane → EuclideanSpace ℝ (Fin m) := fun j =>
    mollifierEps (hε j) ⋆[lsmul ℝ ℝ, volume] Q
  have hv (j : ℕ) : ContDiff ℝ ∞ (v j) :=
    (mollifierEps_compactSupport (hε j)).contDiff_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_smooth (hε j)) hUl
  have hq (j : ℕ) : ContDiff ℝ ∞ (q j) :=
    (mollifierEps_compactSupport (hε j)).contDiff_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_smooth (hε j)) hQl
  have hd (j : ℕ) (x : Plane) (hx : x ∈ I) :
      fderiv ℝ (v j) x (EuclideanSpace.single i 1) = q j x := by
    apply suWeak_convolution_fderiv Metric.isOpen_ball.measurableSet (hw i) hUl hQl
      (mollifierEps_smooth (hε j)) (mollifierEps_compactSupport (hε j))
    rw [suMollifier_translated_tsupport]
    intro y hy
    have hy' := Metric.mem_closedBall.mp hy
    have hx' := Metric.mem_ball.mp hx
    exact Metric.mem_ball.mpr (by linarith [dist_triangle y x a, hεb j])
  have hsub : I ⊆ O := Metric.ball_subset_ball hrR.le
  have hvl : Tendsto (fun j => eLpNorm (v j - u) 4 (volume.restrict I)) atTop (𝓝 0) :=
    restrict_limit Metric.isOpen_ball.measurableSet (fun x hx => indicator_of_mem (hsub hx) u)
      (suVectorMollifier_Lp_tendsto (by norm_num) (by norm_num) hU hε hεz)
  have hql : Tendsto (fun j => eLpNorm (q j - W i) 2 (volume.restrict I)) atTop (𝓝 0) :=
    restrict_limit Metric.isOpen_ball.measurableSet
      (fun x hx => indicator_of_mem (hsub hx) (W i))
      (suVectorMollifier_Lp_tendsto (by norm_num) (by norm_num) hQ hε hεz)
  let : IsFiniteMeasure (volume.restrict I) :=
    ⟨by simpa only [I, Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball a r) < ⊤)⟩
  have hvLp (j : ℕ) : MemLp (v j) 4 (volume.restrict I) :=
    suContinuous_memLp_ball (hv j).continuous.continuousOn
  have hqLp (j : ℕ) : MemLp (q j) 2 (volume.restrict I) :=
    suContinuous_memLp_ball (hq j).continuous.continuousOn
  have huI : MemLp u 4 (volume.restrict I) := hu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hWI : MemLp (W i) 2 (volume.restrict I) :=
    (hW i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hbase (z : EuclideanSpace ℝ (Fin m)) (w : EuclideanSpace ℝ (Fin m)) :
      ‖F z‖ ≤ (C + ‖F 0‖ + 1) * (1 + ‖z‖ ^ 4 + ‖w‖ ^ 2) :=
    (suQuadraticDerivative_value_bound hF hC hDF z).trans
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖w‖]) (by positivity))
  have hderiv (z : EuclideanSpace ℝ (Fin m)) (w : EuclideanSpace ℝ (Fin m)) :
      ‖fderiv ℝ F z w‖ ≤ C * (1 + ‖z‖ ^ 4 + ‖w‖ ^ 2) := by
    have hb := (fderiv ℝ F z).le_opNorm w |>.trans
      (mul_le_mul_of_nonneg_right (hDF z) (norm_nonneg w))
    have hp : (1 + ‖z‖ ^ 2) * ‖w‖ ≤ 1 + ‖z‖ ^ 4 + ‖w‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖w‖ - 1), sq_nonneg (‖w‖ - ‖z‖ ^ 2)]
    exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hC.le])
  have hDFc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hAc : Continuous (fun z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
      fderiv ℝ F z.1 z.2) := (hDFc.comp continuous_fst).clm_apply continuous_snd
  obtain ⟨hvalj, hval0, hvalLim⟩ := suMixedGrowth_L1_limit hvLp huI hqLp hWI hvl hql
    (fun _ z => F z.1)
    (Eventually.of_forall fun _ => (hF.continuous.comp continuous_fst).continuousAt)
    (fun j => (hF.continuous.comp (hv j).continuous).aestronglyMeasurable)
    (hF.continuous.comp_aestronglyMeasurable huI.1) (by positivity : 0 < C + ‖F 0‖ + 1)
    (fun j => Eventually.of_forall fun x => hbase (v j x) (q j x))
    (Eventually.of_forall fun x => hbase (u x) (W i x))
  obtain ⟨hgradj, hgrad0, hgradLim⟩ := suMixedGrowth_L1_limit hvLp huI hqLp hWI hvl hql
    (fun _ z => fderiv ℝ F z.1 z.2) (Eventually.of_forall fun _ => hAc.continuousAt)
    (fun j => ((hDFc.comp (hv j).continuous).clm_apply (hq j).continuous).aestronglyMeasurable)
    (hAc.comp_aestronglyMeasurable (huI.1.prodMk hWI.1)) hC
    (fun j => Eventually.of_forall fun x => hderiv (v j x) (q j x))
    (Eventually.of_forall fun x => hderiv (u x) (W i x))
  apply suWeakPartial_of_L1_approx hval0 hgrad0 hvalj hgradj (fun j => ?_) hvalLim hgradLim
  have hcomp : ContDiff ℝ 1 (fun x => F (v j x)) := hF.comp ((hv j).of_le (by simp))
  apply suWeakPartial_congr_ae (HasWeakPartialDeriv.of_contDiff (i := i) Metric.isOpen_ball hcomp)
    Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  have he := (hF.differentiable (by norm_num) (v j x)).hasFDerivAt.comp x
    ((hv j).differentiable (by simp) x).hasFDerivAt
  change HasFDerivAt (fun y => F (v j y)) _ x at he
  rw [he.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hd j x hx]

end PoincareConjecture.M60

end
