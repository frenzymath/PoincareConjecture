import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityExtension
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalInterface
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByParts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem puncture_cutoffs :
    ∃ (χ : ℕ → LoopPlane → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ j, ContDiff ℝ ∞ (χ j) ∧ χ j =ᶠ[𝓝 0] 0 ∧
        (∀ z, 0 ≤ χ j z ∧ χ j z ≤ 1) ∧
        ∀ z ≠ 0, ‖fderiv ℝ (χ j) z‖ ≤ C / ‖z‖) ∧
      ∀ z ≠ 0, ∀ᶠ j in atTop, χ j z = 1 ∧ fderiv ℝ (χ j) z = 0 := by
  let b : ContDiffBump (0 : LoopPlane) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hb : ContDiff ℝ ∞ b := b.contDiff
  obtain ⟨A, hA⟩ := (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  let B := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  have hBd (z : LoopPlane) : ‖fderiv ℝ b z‖ ≤ B := (hA z).trans (le_max_left _ _)
  let χ := fun (j : ℕ) (z : LoopPlane) => 1 - b (((j : ℝ) + 1) • z)
  have hd (j : ℕ) (z : LoopPlane) : fderiv ℝ (χ j) z =
      (-((j : ℝ) + 1)) • fderiv ℝ b (((j : ℝ) + 1) • z) := by
    have hh := (hasFDerivAt_const (1 : ℝ) z).sub
      (((hb.differentiable (by simp)) _).hasFDerivAt.comp z
        ((hasFDerivAt_id z).const_smul ((j : ℝ) + 1)))
    convert! hh.fderiv using 1
    ext v
    simp only [zero_sub, neg_apply, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, neg_mul, Pi.smul_apply, id_eq]
  refine ⟨χ, 2 * B, by positivity, fun j => ?_, fun z hz => ?_⟩
  · have hj : 0 < (j : ℝ) + 1 := by positivity
    have hsmooth : ContDiff ℝ ∞ (fun z : LoopPlane => ((j : ℝ) + 1) • z) :=
      (((j : ℝ) + 1) • ContinuousLinearMap.id ℝ LoopPlane).contDiff
    refine ⟨contDiff_const.sub (hb.comp hsmooth), ?_,
      (fun z => ⟨sub_nonneg.mpr b.le_one, sub_le_self _ b.nonneg⟩), ?_⟩
    · have hs : Tendsto (fun z : LoopPlane => ((j : ℝ) + 1) • z) (𝓝 0) (𝓝 0) := by
        simpa only [smul_zero] using
          hsmooth.continuous.tendsto (0 : LoopPlane)
      filter_upwards [b.eventuallyEq_one.comp_tendsto hs] with z hz
      change b (((j : ℝ) + 1) • z) = 1 at hz
      change 1 - b (((j : ℝ) + 1) • z) = 0
      rw [hz, sub_self]
    · intro z hz
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      by_cases hs : ‖((j : ℝ) + 1) • z‖ ≤ 2
      · have hs' : ((j : ℝ) + 1) * ‖z‖ ≤ 2 := by
          simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hj] using hs
        rw [hd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hj]
        calc
          _ ≤ ((j : ℝ) + 1) * B := mul_le_mul_of_nonneg_left (hBd _) hj.le
          _ ≤ 2 * B / ‖z‖ := (le_div_iff₀ hn).mpr (by nlinarith only [hs', hB])
      · have hout : ((j : ℝ) + 1) • z ∉ tsupport (b : LoopPlane → ℝ) := by
          simpa only [b.tsupport_eq, mem_closedBall_zero_iff] using hs
        rw [hd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hout, smul_zero, norm_zero]
        positivity
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_gt_atTop (2 / ‖z‖))] with j hj
    have hs : 2 < ‖((j : ℝ) + 1) • z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (j : ℝ) + 1)]
      have hh := (div_lt_iff₀ hn).mp hj
      nlinarith only [hh, hn]
    have hout : ((j : ℝ) + 1) • z ∉ tsupport (b : LoopPlane → ℝ) := by
      simpa only [b.tsupport_eq, mem_closedBall_zero_iff, not_le] using hs
    constructor
    · dsimp only [χ]
      rw [image_eq_zero_of_notMem_tsupport hout, sub_zero]
    · rw [hd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hout, smul_zero]

private theorem puncture_variation_extend
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Fin 2 → LoopPlane → E →L[ℝ] ℝ} {b : LoopPlane → E →L[ℝ] ℝ} {r : ℝ}
    (hF : ∀ i, IntegrableOn (F i) (Metric.ball (0 : LoopPlane) r))
    (hb : IntegrableOn b (Metric.ball (0 : LoopPlane) r))
    (hFr : ∀ i, IntegrableOn (fun z => ‖F i z‖ / ‖z‖) (Metric.ball (0 : LoopPlane) r))
    (heq : ∀ η : LoopPlane → E, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Metric.ball (0 : LoopPlane) r \ {0} →
      (∫ z in Metric.ball (0 : LoopPlane) r, b z (η z) +
        ∑ i : Fin 2, F i z (fderiv ℝ η z (EuclideanSpace.basisFun (Fin 2) ℝ i))) = 0)
    {η : LoopPlane → E} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Metric.ball (0 : LoopPlane) r) :
    IntegrableOn (fun z => b z (η z) +
      ∑ i : Fin 2, F i z (fderiv ℝ η z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
        (Metric.ball (0 : LoopPlane) r) ∧
    (∫ z in Metric.ball (0 : LoopPlane) r, b z (η z) +
      ∑ i : Fin 2, F i z (fderiv ℝ η z (EuclideanSpace.basisFun (Fin 2) ℝ i))) = 0 := by
  obtain ⟨χ, C, hC, hχ, hχlim⟩ := puncture_cutoffs
  obtain ⟨A, hA⟩ := hη.continuous.bounded_above_of_compact_support hηc
  obtain ⟨D, hD⟩ := (hη.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hηc.fderiv (𝕜 := ℝ))
  have hA0 : 0 ≤ A := (norm_nonneg (η 0)).trans (hA 0)
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ η 0)).trans (hD 0)
  let v := fun (j : ℕ) (z : LoopPlane) => χ j z • η z
  have hv (j) : ContDiff ℝ ∞ (v j) := (hχ j).1.smul hη
  have hvc (j) : HasCompactSupport (v j) := hηc.smul_left
  have hvs (j) : tsupport (v j) ⊆ Metric.ball (0 : LoopPlane) r \ {0} := by
    intro z hz
    refine ⟨hηs (tsupport_smul_subset_right (χ j) η hz), ?_⟩
    intro hz0
    have he : v j =ᶠ[𝓝 (0 : LoopPlane)] 0 := by
      filter_upwards [(hχ j).2.1] with y hy
      simp only [v, hy, Pi.zero_apply, zero_smul]
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) (mem_singleton_iff.mp hz0 ▸ hz)
  have hd (j) (z : LoopPlane) (i : Fin 2) :
      fderiv ℝ (v j) z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        χ j z • fderiv ℝ η z (EuclideanSpace.basisFun (Fin 2) ℝ i) +
        fderiv ℝ (χ j) z (EuclideanSpace.basisFun (Fin 2) ℝ i) • η z := by
    rw [show v j = fun y => χ j y • η y from rfl,
      fderiv_fun_smul ((hχ j).1.differentiable (by simp) z) (hη.differentiable (by simp) z)]
    rfl
  have hval (j) (z : LoopPlane) : ‖v j z‖ ≤ A := by
    have hc : ‖χ j z‖ ≤ 1 := by
      rw [Real.norm_of_nonneg ((hχ j).2.2.1 z).1]
      exact ((hχ j).2.2.1 z).2
    exact (norm_smul _ _).le.trans
      ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by simpa using hA z))
  have hder (j) {z : LoopPlane} (hz : z ≠ 0) (i : Fin 2) :
      ‖fderiv ℝ (v j) z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ D + A * C / ‖z‖ := by
    have hc : ‖χ j z‖ ≤ 1 := by
      rw [Real.norm_of_nonneg ((hχ j).2.2.1 z).1]
      exact ((hχ j).2.2.1 z).2
    have hdc : ‖fderiv ℝ (χ j) z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ C / ‖z‖ := by
      exact ((fderiv ℝ (χ j) z).le_opNorm _).trans
        (by simpa only [OrthonormalBasis.norm_eq_one, mul_one] using (hχ j).2.2.2 z hz)
    have hdη : ‖fderiv ℝ η z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ D := by
      exact ((fderiv ℝ η z).le_opNorm _).trans
        (by simpa only [OrthonormalBasis.norm_eq_one, mul_one] using hD z)
    rw [hd]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul]
    have h1 := mul_le_mul hc hdη (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)
    have h2 := mul_le_mul hdc (hA z) (norm_nonneg _) (div_nonneg hC (norm_nonneg _))
    exact (add_le_add h1 h2).trans_eq (by ring)
  let L := fun (w : LoopPlane → E) (z : LoopPlane) => b z (w z) +
    ∑ i : Fin 2, F i z (fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i))
  let H := fun z => A * ‖b z‖ + ∑ i : Fin 2,
    (D * ‖F i z‖ + (A * C) * (‖F i z‖ / ‖z‖))
  have hi : IntegrableOn H (Metric.ball (0 : LoopPlane) r) :=
    (hb.norm.const_mul A).add (integrable_finsetSum _ (fun i _ =>
      ((hF i).norm.const_mul D).add ((hFr i).const_mul (A * C))))
  have hm {w : LoopPlane → E} (hw : ContDiff ℝ ∞ w) :
      AEStronglyMeasurable (L w) (volume.restrict (Metric.ball (0 : LoopPlane) r)) := by
    have heval : Continuous (fun p : (E →L[ℝ] ℝ) × E => p.1 p.2) := by fun_prop
    apply (heval.comp_aestronglyMeasurable
      (hb.aestronglyMeasurable.prodMk hw.continuous.aestronglyMeasurable)).add
    have hdw (i : Fin 2) : AEStronglyMeasurable
        (fun z => fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (volume.restrict (Metric.ball (0 : LoopPlane) r)) :=
      ((hw.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    simp only [Fin.sum_univ_two]
    exact (heval.comp_aestronglyMeasurable
      ((hF 0).aestronglyMeasurable.prodMk (hdw 0))).add
      (heval.comp_aestronglyMeasurable ((hF 1).aestronglyMeasurable.prodMk (hdw 1)))
  have hbound (j) {z : LoopPlane} (hz : z ≠ 0) : ‖L (v j) z‖ ≤ H z := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact ((b z).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left (hval j z) (norm_nonneg _)).trans_eq (mul_comm _ _))
    · apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
      exact ((F i z).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left (hder j hz i) (norm_nonneg _)).trans_eq (by ring))
  have hlim {z : LoopPlane} (hz : z ≠ 0) :
      Tendsto (fun j => L (v j) z) atTop (𝓝 (L η z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hχlim z hz] with j hj
    simp only [L, v, hj.1, one_smul, hd, hj.2, zero_apply, zero_smul, add_zero]
  have hlim' : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : LoopPlane) r),
      Tendsto (fun j => L (v j) z) atTop (𝓝 (L η z)) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : LoopPlane))] with z hz
    exact hlim hz
  have hbound' (j) : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : LoopPlane) r),
      ‖L (v j) z‖ ≤ H z := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : LoopPlane))] with z hz
    exact hbound j hz
  have ht := tendsto_integral_of_dominated_convergence H (fun j => hm (hv j)) hi hbound' hlim'
  have hli : IntegrableOn (L η) (Metric.ball (0 : LoopPlane) r) := by
    apply hi.mono' (hm hη)
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : LoopPlane))] with z hz
    exact le_of_tendsto (hlim hz).norm (Eventually.of_forall (fun j => hbound j hz))
  refine ⟨hli, ?_⟩
  exact tendsto_nhds_unique ht (by
    simp only [L, heq (v _) (hv _) (hvc _) (hvs _)]
    exact tendsto_const_nhds)

private theorem puncture_radial_power_integrable {a r : ℝ} (ha : -2 < a) :
    IntegrableOn (fun z : LoopPlane => ‖z‖ ^ a) (Metric.ball (0 : LoopPlane) r) := by
  have hm : Measurable (fun z : LoopPlane => ‖z‖ ^ a) := by fun_prop
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := -a) (by simp)
    (by simpa using neg_lt_neg ha) ?_ hm.aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      neg_neg, one_mul, le_refl])

private theorem puncture_column_div_integrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {V : LoopPlane → E} {B κ r : ℝ}
    (hV : AEStronglyMeasurable V volume) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hbound : ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0},
      ‖V z‖ ^ 2 ≤ B * ‖z‖ ^ (κ - 2)) :
    IntegrableOn (fun z => ‖V z‖ / ‖z‖) (Metric.ball (0 : LoopPlane) r) := by
  have hi := (puncture_radial_power_integrable (r := r)
    (a := (κ - 2) / 2 - 1) (by linarith only [hκ])).const_mul (B ^ (1 / 2 : ℝ))
  apply hi.mono'
    ((hV.norm.aemeasurable.div measurable_norm.aemeasurable).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0 : LoopPlane))] with z hz hne
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hne
  have hh := Real.rpow_le_rpow (sq_nonneg ‖V z‖) (hbound z ⟨hz, hne⟩)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have he : (‖V z‖ ^ 2) ^ (1 / 2 : ℝ) = ‖V z‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [he, Real.mul_rpow hB (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _)] at hh
  dsimp only [Pi.div_apply]
  rw [norm_div, norm_norm, norm_norm]
  apply (div_le_div_of_nonneg_right hh hn.le).trans_eq
  rw [Real.rpow_sub hn, Real.rpow_one,
    show (κ - 2) * (1 / 2 : ℝ) = (κ - 2) / 2 by ring]
  ring

private theorem puncture_weak_partial {f h : LoopPlane → ℝ} {r : ℝ} (i : Fin 2)
    (hf : ContinuousOn f (Metric.closedBall (0 : LoopPlane) r))
    (hs : ContDiffOn ℝ ∞ f (Metric.ball (0 : LoopPlane) r \ {0}))
    (hi : IntegrableOn h (Metric.ball (0 : LoopPlane) r))
    (hd : ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0},
      h z = fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i h f
      (Metric.ball (0 : LoopPlane) r) := by
  classical
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : LoopPlane) r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hfm : AEStronglyMeasurable f (volume.restrict (Metric.ball (0 : LoopPlane) r)) :=
    (hf.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : LoopPlane) r).bddAbove_image hf.norm
  have hfa : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : LoopPlane) r), ‖f z‖ ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hA (mem_image_of_mem _ (Metric.ball_subset_closedBall hz))
  have hfi : IntegrableOn f (Metric.ball (0 : LoopPlane) r) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hfm A hfa)
  have hfr : IntegrableOn (fun z => ‖f z‖ / ‖z‖) (Metric.ball (0 : LoopPlane) r) := by
    apply ((puncture_radial_power_integrable (r := r) (a := -1) (by norm_num)).const_mul A).mono'
      ((hfm.norm.aemeasurable.div measurable_norm.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfa] with z hz
    dsimp only [Pi.div_apply]
    rw [norm_div, norm_norm, norm_norm, Real.rpow_neg_one, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hz (norm_nonneg _)
  let b := fun z => h z • ContinuousLinearMap.id ℝ ℝ
  let F := fun (j : Fin 2) z => (if j = i then f z else 0) • ContinuousLinearMap.id ℝ ℝ
  have hb : IntegrableOn b (Metric.ball (0 : LoopPlane) r) := hi.smul_const _
  have hF (j : Fin 2) : IntegrableOn (F j) (Metric.ball (0 : LoopPlane) r) := by
    dsimp only [IntegrableOn, F]
    by_cases hj : j = i
    · simp only [if_pos hj]
      exact hfi.smul_const (ContinuousLinearMap.id ℝ ℝ)
    · simp only [if_neg hj, zero_smul]
      exact integrable_zero LoopPlane (ℝ →L[ℝ] ℝ)
        (volume.restrict (Metric.ball (0 : LoopPlane) r))
  have hFr (j : Fin 2) : IntegrableOn (fun z => ‖F j z‖ / ‖z‖)
      (Metric.ball (0 : LoopPlane) r) := by
    by_cases hj : j = i
    · simpa only [F, if_pos hj, norm_smul, ContinuousLinearMap.norm_id, mul_one] using hfr
    · simp only [F, if_neg hj, zero_smul, norm_zero, zero_div]
      exact integrable_zero _ _ _
  have hL (w : LoopPlane → ℝ) (z : LoopPlane) : b z (w z) +
      ∑ j : Fin 2, F j z (fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
        h z * w z + f z * fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    fin_cases i <;> simp [F, b, Fin.sum_univ_two]
  have heq (w : LoopPlane → ℝ) (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
      (hws : tsupport w ⊆ Metric.ball (0 : LoopPlane) r \ {0}) :
      (∫ z in Metric.ball (0 : LoopPlane) r, b z (w z) +
        ∑ j : Fin 2, F j z (fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ j))) = 0 := by
    let q := fun z => f z * w z
    have hqs : Function.support q ⊆ tsupport w := by
      intro z hz
      apply subset_tsupport
      intro hzero
      exact hz (by simp only [q, hzero, mul_zero])
    have hqt : tsupport q ⊆ tsupport w := closure_minimal hqs (isClosed_tsupport w)
    have hq : ContDiff ℝ ∞ q := contDiff_of_support_subset_closed (isClosed_tsupport w)
      (Metric.isOpen_ball.sdiff isClosed_singleton) hws (hs.mul hw.contDiffOn) hqs
    have hqc : HasCompactSupport q := hwc.mul_left
    have hder (z : LoopPlane) : fderiv ℝ q z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        h z * w z + f z * fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      by_cases hz : z ∈ tsupport w
      · have hfs := hs.contDiffAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds (hws hz))
        rw [hd z (hws hz), show q = fun y => f y * w y from rfl,
          fderiv_fun_mul (hfs.differentiableAt (by simp)) (hw.differentiable (by simp) z)]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      · rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hz (hqt h)),
          image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
        simp only [zero_apply, mul_zero, add_zero]
    simp_rw [hL, ← hder]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hz ((hws (hqt h)).1)), zero_apply])]
    exact integral_fderiv_eq_zero_of_hasCompactSupport hq hqc _
  intro w hw hwc hws
  obtain ⟨_, hz⟩ := puncture_variation_extend hF hb hFr heq hw hwc hws
  simp_rw [hL] at hz
  have hg : IntegrableOn (fun z => h z * w z) (Metric.ball (0 : LoopPlane) r) := by
    dsimp only [IntegrableOn]
    simpa only [smul_eq_mul] using
      hi.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hw.continuous hwc
  have hg' : IntegrableOn
      (fun z => f z * fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (Metric.ball (0 : LoopPlane) r) := by
    dsimp only [IntegrableOn]
    simpa only [smul_eq_mul] using
      hfi.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
        ((hw.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hwc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin 2) ℝ i))
  rw [integral_add hg hg'] at hz
  simp only [EuclideanSpace.basisFun_apply] at hz
  linarith only [hz]

local instance epsilonRemovalBilinearNormedAddCommGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance epsilonRemovalBilinearNormedSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance epsilonRemovalTrilinearNormedAddCommGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance epsilonRemovalTrilinearNormedSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1600000 in

private theorem puncture_variation_coefficients (g : RiemannianMetric n M) (p : M)
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {r q B κ : ℝ}
    (hu : ContinuousOn u (Metric.closedBall (0 : LoopPlane) r))
    (hrange : MapsTo u (Metric.closedBall (0 : LoopPlane) r) (extChartAt (𝓡 n) p).target)
    (hq : 2 < q) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hV : ∀ i : Fin 2, MemLp
      (fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (ENNReal.ofReal q) (volume.restrict (Metric.ball (0 : LoopPlane) r)))
    (hpow : ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0}, ∀ i : Fin 2,
      ‖fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 ≤ B * ‖z‖ ^ (κ - 2)) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
    let V := fun i z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)
    let F := fun i z => (2 : ℝ) • G (u z) (V i z)
    let b := fun z => ∑ i : Fin 2, ((fderiv ℝ G (u z)).flip (V i z)).flip (V i z)
    (∀ i, IntegrableOn (F i) (Metric.ball (0 : LoopPlane) r)) ∧
      IntegrableOn b (Metric.ball (0 : LoopPlane) r) ∧
      ∀ i, IntegrableOn (fun z => ‖F i z‖ / ‖z‖) (Metric.ball (0 : LoopPlane) r) := by
  let E := EuclideanSpace ℝ (Fin n)
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  let V := fun i z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let F := fun i z => (2 : ℝ) • G (u z) (V i z)
  let b := fun z => ∑ i : Fin 2, ((fderiv ℝ G (u z)).flip (V i z)).flip (V i z)
  let μ := volume.restrict (Metric.ball (0 : LoopPlane) r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hGc : ContinuousOn (fun z => G (u z)) (Metric.closedBall (0 : LoopPlane) r) :=
    (g.contDiffOn_chartCoefficients p).continuousOn.comp hu hrange
  have hDc : ContinuousOn (fun z => fderiv ℝ G (u z))
      (Metric.closedBall (0 : LoopPlane) r) :=
    ((g.contDiffOn_chartCoefficients p).continuousOn_fderiv_of_isOpen
      (isOpen_extChartAt_target p) (by simp)).comp hu hrange
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : LoopPlane) r).bddAbove_image hGc.norm
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : LoopPlane) r).bddAbove_image hDc.norm
  let C := max A (max D 0)
  have hC : 0 ≤ C := (le_max_right D 0).trans (le_max_right A _)
  have hc (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) r) :
      ‖G (u z)‖ ≤ C ∧ ‖fderiv ℝ G (u z)‖ ≤ C := by
    have hz' := Metric.ball_subset_closedBall hz
    exact ⟨(hA (mem_image_of_mem _ hz')).trans (le_max_left _ _),
      (hD (mem_image_of_mem _ hz')).trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  have hGm : AEStronglyMeasurable (fun z => G (u z)) μ :=
    (hGc.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hDm : AEStronglyMeasurable (fun z => fderiv ℝ G (u z)) μ :=
    (hDc.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hVm (i : Fin 2) : AEStronglyMeasurable (V i) volume :=
    (measurable_fderiv_apply_const ℝ u _).aestronglyMeasurable
  have hV2 (i : Fin 2) : MemLp (V i) 2 μ := (hV i).mono_exponent
    (by simpa using ENNReal.ofReal_le_ofReal hq.le)
  have hVi (i : Fin 2) : Integrable (V i) μ := (hV2 i).integrable (by norm_num)
  have hVs (i : Fin 2) : Integrable (fun z => ‖V i z‖ ^ 2) μ :=
    (hV2 i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hVr (i : Fin 2) : Integrable (fun z => ‖V i z‖ / ‖z‖) μ :=
    puncture_column_div_integrable (hVm i) hB hκ (fun z hz => hpow z hz i)
  have hFm (i : Fin 2) : AEStronglyMeasurable (F i) μ := by
    have hh : AEStronglyMeasurable (fun z => G (u z) (V i z)) μ :=
      (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
        hGm (hV2 i).aestronglyMeasurable
    exact hh.const_smul (2 : ℝ)
  have hFm_bound (i : Fin 2) {z : LoopPlane} (hz : z ∈ Metric.ball (0 : LoopPlane) r) :
      ‖F i z‖ ≤ (2 * C) * ‖V i z‖ := by
    dsimp only [F]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact (mul_le_mul_of_nonneg_left ((G (u z)).le_opNorm _) (by norm_num)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right (hc z hz).1 (norm_nonneg (V i z))])
  have hbi (i : Fin 2) : AEStronglyMeasurable
      (fun z => ((fderiv ℝ G (u z)).flip (V i z)).flip (V i z)) μ := by
    have h0 : AEStronglyMeasurable (fun z => (fderiv ℝ G (u z)).flip) μ :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable hDm
    have h1 : AEStronglyMeasurable (fun z => (fderiv ℝ G (u z)).flip (V i z)) μ :=
      (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
        h0 (hV2 i).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z => ((fderiv ℝ G (u z)).flip (V i z)).flip) μ :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous.comp_aestronglyMeasurable h1
    exact (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
      h2 (hV2 i).aestronglyMeasurable
  have hbm : AEStronglyMeasurable b μ := by
    dsimp only [b]
    simp only [Fin.sum_univ_two]
    exact (hbi 0).add (hbi 1)
  have hb_bound {z : LoopPlane} (hz : z ∈ Metric.ball (0 : LoopPlane) r) :
      ‖b z‖ ≤ ∑ i : Fin 2, C * ‖V i z‖ ^ 2 := by
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    calc
      _ ≤ ‖((fderiv ℝ G (u z)).flip (V i z)).flip‖ * ‖V i z‖ :=
        (((fderiv ℝ G (u z)).flip (V i z)).flip).le_opNorm _
      _ = ‖(fderiv ℝ G (u z)).flip (V i z)‖ * ‖V i z‖ := by
        rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖(fderiv ℝ G (u z)).flip‖ * ‖V i z‖) * ‖V i z‖ :=
        mul_le_mul_of_nonneg_right (((fderiv ℝ G (u z)).flip).le_opNorm _) (norm_nonneg _)
      _ ≤ C * ‖V i z‖ ^ 2 := by
        rw [ContinuousLinearMap.opNorm_flip]
        nlinarith [mul_le_mul_of_nonneg_right (hc z hz).2 (sq_nonneg ‖V i z‖)]
  refine ⟨fun i => ?_, ?_, fun i => ?_⟩
  · apply ((hVi i).norm.const_mul (2 * C)).mono' (hFm i)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hFm_bound i hz
  · have hsum : Integrable (fun z => ∑ i : Fin 2, C * ‖V i z‖ ^ 2) μ :=
      integrable_finsetSum _ (fun i _ => (hVs i).const_mul C)
    apply hsum.mono' hbm
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hb_bound hz
  · apply ((hVr i).const_mul (2 * C)).mono'
      (((hFm i).norm.aemeasurable.div measurable_norm.aemeasurable).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    dsimp only [Pi.div_apply]
    rw [norm_div, norm_norm, norm_norm]
    exact (div_le_div_of_nonneg_right (hFm_bound i hz) (norm_nonneg _)).trans_eq (by ring)

open CoordinateExponential ConnectionVariation ConjugateVariation
set_option maxHeartbeats 1600000 in

private theorem puncture_harmonic_variation (g : RiemannianMetric n M) (p : M)
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {r q B κ : ℝ}
    (hu : ContinuousOn u (Metric.closedBall (0 : LoopPlane) r))
    (hus : ContDiffOn ℝ ∞ u (Metric.ball (0 : LoopPlane) r \ {0}))
    (hrange : MapsTo u (Metric.closedBall (0 : LoopPlane) r) (extChartAt (𝓡 n) p).target)
    (hq : 2 < q) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hV : ∀ i : Fin 2, MemLp
      (fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (ENNReal.ofReal q) (volume.restrict (Metric.ball (0 : LoopPlane) r)))
    (hpow : ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0}, ∀ i : Fin 2,
      ‖fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 ≤ B * ‖z‖ ^ (κ - 2))
    (hharm : ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0},
      let Γ := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
      ∑ i : Fin 2, covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0)
    {η : LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Metric.ball (0 : LoopPlane) r) :
    let V := fun i z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)
    IntegrableOn (suAlphaChartVariation g p 1 u V η) (Metric.ball (0 : LoopPlane) r) ∧
      (∫ z in Metric.ball (0 : LoopPlane) r, suAlphaChartVariation g p 1 u V η z) = 0 := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  let Γ := christoffelBilinear G
  let V := fun i z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let F := fun i z => (2 : ℝ) • G (u z) (V i z)
  let b := fun z => ∑ i : Fin 2, ((fderiv ℝ G (u z)).flip (V i z)).flip (V i z)
  let O := Metric.ball (0 : LoopPlane) r \ {0}
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have ht (z : LoopPlane) (hz : z ∈ O) : u z ∈ (extChartAt (𝓡 n) p).target :=
    hrange (Metric.ball_subset_closedBall hz.1)
  have hG (z : LoopPlane) (hz : z ∈ O) : ContDiffAt ℝ ∞ G (u z) :=
    (g.contDiffOn_chartCoefficients p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds (ht z hz))
  have hΓ (z : LoopPlane) (hz : z ∈ O) : ContDiffAt ℝ ∞ Γ (u z) :=
    contDiffAt_christoffelBilinear (hG z hz) (g.isInvertible_chartCoefficients p (ht z hz))
  have hcompat (z : LoopPlane) (hz : z ∈ O) : IsMetricCompatibleAt G Γ (u z) :=
    isMetricCompatibleAt_chartCoefficients g p (ht z hz)
  have hL (w : LoopPlane → EuclideanSpace ℝ (Fin n)) (z : LoopPlane) :
      suAlphaChartVariation g p 1 u V w z = b z (w z) +
        ∑ i : Fin 2, F i z (fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
    simp only [suAlphaChartVariation, sub_self, Real.rpow_zero, one_mul]
    change (∑ i : Fin 2, fderiv ℝ G (u z) (w z) (V i z) (V i z)) +
      2 * ∑ i : Fin 2, G (u z) (V i z)
        (fderiv ℝ w z (EuclideanSpace.single i 1)) = _
    simp only [b, F, Fin.sum_univ_two, add_apply, ContinuousLinearMap.flip_apply,
      smul_apply, smul_eq_mul, EuclideanSpace.basisFun_apply]
    ring
  obtain ⟨hFi, hbi, hFri⟩ := puncture_variation_coefficients g p hu hrange hq hB hκ hV hpow
  have heq (w : LoopPlane → EuclideanSpace ℝ (Fin n))
      (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) (hws : tsupport w ⊆ O) :
      (∫ z in Metric.ball (0 : LoopPlane) r, b z (w z) +
        ∑ i : Fin 2, F i z (fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i))) = 0 := by
    let P := fun z => ∑ i : Fin 2, G (u z)
      (covDerivAlong Γ u w (EuclideanSpace.basisFun (Fin 2) ℝ i) z) (V i z)
    have hi := covDerivAlong_trace_integration_by_parts (μ := volume)
      (EuclideanSpace.basisFun (Fin 2) ℝ) hO hus hw.contDiffOn hG hΓ hcompat hwc hws
    have hzero (z : LoopPlane) : G (u z) (w z)
        (∑ i : Fin 2, covDerivAlong Γ u (V i) (EuclideanSpace.basisFun (Fin 2) ℝ i) z) = 0 := by
      by_cases hz : z ∈ O
      · rw [hharm z hz]
        exact map_zero _
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hws h)), map_zero, zero_apply]
    have hPi : (∫ z, P z) = 0 := by
      have hh := hi.2.2
      change (∫ z, P z) = -(∫ z, G (u z) (w z)
        (∑ i : Fin 2, covDerivAlong Γ u (V i) (EuclideanSpace.basisFun (Fin 2) ℝ i) z)) at hh
      simpa only [hzero, integral_zero, neg_zero] using hh
    have hpoint (z : LoopPlane) : b z (w z) +
        ∑ i : Fin 2, F i z (fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 2 * P z := by
      by_cases hz : z ∈ O
      · have hterm (i : Fin 2) : fderiv ℝ G (u z) (w z) (V i z) (V i z) +
            2 * G (u z) (V i z) (fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            2 * G (u z) (covDerivAlong Γ u w (EuclideanSpace.basisFun (Fin 2) ℝ i) z)
              (V i z) := by
          rw [hcompat z hz (w z) (V i z) (V i z)]
          have hsym (a c : EuclideanSpace ℝ (Fin n)) : G (u z) a c = G (u z) c a := g.symm _ _ _
          have hΓsym := christoffelBilinear_chart_symm g p (u z) (w z) (V i z)
          dsimp only [covDerivAlong_def]
          rw [hΓsym, hsym (V i z) (Γ (u z) (V i z) (w z)),
            hsym (V i z) (fderiv ℝ w z (EuclideanSpace.basisFun (Fin 2) ℝ i))]
          simp only [map_add, add_apply]
          dsimp only [Γ, G, V]
          ring
        have h0 := hterm 0
        have h1 := hterm 1
        simp only [b, F, P, Fin.sum_univ_two, add_apply, ContinuousLinearMap.flip_apply,
          smul_apply, smul_eq_mul]
        linarith only [h0, h1]
      · have hwz := image_eq_zero_of_notMem_tsupport (fun h => hz (hws h))
        have hwd := fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hz (hws h))
        simp only [b, F, P, hwz, hwd, covDerivAlong_def, zero_apply, map_zero,
          add_zero, Finset.sum_const_zero, mul_zero]
    simp_rw [hpoint]
    rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have hnot : z ∉ tsupport w := fun h => hz (hws h).1
      simp only [P, covDerivAlong_def, image_eq_zero_of_notMem_tsupport hnot,
        fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, zero_apply, map_zero, add_zero,
        Finset.sum_const_zero]), hPi, mul_zero]
  obtain ⟨hi, hz⟩ := puncture_variation_extend hFi hbi hFri heq hη hηc hηs
  exact ⟨hi.congr_fun (fun z _ => (hL η z).symm) measurableSet_ball,
    (setIntegral_congr_fun measurableSet_ball (fun z _ => hL η z)).trans hz⟩

set_option maxHeartbeats 1600000 in

theorem suHarmonicPuncture_removable_weak [CompactSpace M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {φ : LoopPlane → M}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ (Metric.ball (0 : LoopPlane) 1 \ {0}))
    (hharm : ∀ b : M, ∀ z ∈ Metric.ball (0 : LoopPlane) 1 \ {0},
      φ z ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0)
    (hfinite : IntegrableOn (m60EnergyDensity g φ) (Metric.ball (0 : LoopPlane) 1 \ {0})) :
    ∃ (p : M) (r q : ℝ), 0 < r ∧ r < 1 ∧ 2 < q ∧
      let ψ := Function.update φ 0 p
      let u := extChartAt (𝓡 n) p ∘ ψ
      let V := fun i z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)
      ContinuousOn ψ (Metric.ball (0 : LoopPlane) 1) ∧
      MapsTo ψ (Metric.closedBall (0 : LoopPlane) r) (extChartAt (𝓡 n) p).source ∧
      ContinuousOn u (Metric.closedBall (0 : LoopPlane) r) ∧
      MemLp u (ENNReal.ofReal q) (volume.restrict (Metric.ball (0 : LoopPlane) r)) ∧
      (∀ i : Fin 2, MemLp (V i) (ENNReal.ofReal q)
        (volume.restrict (Metric.ball (0 : LoopPlane) r))) ∧
      (∀ (i : Fin 2) (a : Fin n),
        Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i
          (fun z => V i z a) (fun z => u z a) (Metric.ball (0 : LoopPlane) r)) ∧
      ∀ η : LoopPlane → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ η → HasCompactSupport η →
        tsupport η ⊆ Metric.ball (0 : LoopPlane) r →
        IntegrableOn (suAlphaChartVariation g p 1 u V η) (Metric.ball (0 : LoopPlane) r) ∧
          (∫ z in Metric.ball (0 : LoopPlane) r, suAlphaChartVariation g p 1 u V η z) = 0 := by
  classical
  obtain ⟨p, r, q, B, κ, hr, hr1, hq, hB, hκ, hp, hmap, huc, hum, hVm, hpow⟩ :=
    suHarmonicPuncture_chart_integrability D hφ hharm hfinite
  let ψ := Function.update φ 0 p
  let u := extChartAt (𝓡 n) p ∘ ψ
  let V := fun i z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have he {z : LoopPlane} (hz : z ≠ 0) : ψ =ᶠ[𝓝 z] φ := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with y hy
    exact Function.update_of_ne hy p φ
  have hup {z : LoopPlane} (hz : z ∈ Metric.ball (0 : LoopPlane) r \ {0}) :
      ContDiffAt ℝ ∞ u z := by
    have hs := (hφ.contMDiffAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds
      ⟨Metric.ball_subset_ball hr1.le hz.1, hz.2⟩)).congr_of_eventuallyEq (he hz.2)
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) p) (ψ z) :=
      contMDiffAt_extChartAt' (by
        simpa only [extChartAt_source] using (hmap (Metric.ball_subset_closedBall hz.1)))
    exact contMDiffAt_iff_contDiffAt.mp (hc.comp z hs)
  have hus : ContDiffOn ℝ ∞ u (Metric.ball (0 : LoopPlane) r \ {0}) :=
    fun _ hz => (hup hz).contDiffWithinAt
  have htarget : MapsTo u (Metric.closedBall (0 : LoopPlane) r)
      (extChartAt (𝓡 n) p).target := fun _ hz => (extChartAt (𝓡 n) p).map_source (hmap hz)
  have hτ : ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0},
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u (V i)
        (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0 := by
    intro z hz
    let w := extChartAt (𝓡 n) p ∘ φ
    have hw : u =ᶠ[𝓝 z] w := (he hz.2).mono (fun y hy => congrArg (extChartAt (𝓡 n) p) hy)
    have hw' (i : Fin 2) : V i =ᶠ[𝓝 z]
        (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
      (hw.fderiv (𝕜 := ℝ)).mono (fun y hy =>
        congrArg (fun L : LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n) =>
          L (EuclideanSpace.basisFun (Fin 2) ℝ i)) hy)
    have hh := hharm p z ⟨Metric.ball_subset_ball hr1.le hz.1, hz.2⟩
      (by rw [← (he hz.2).eq_of_nhds]; exact hmap (Metric.ball_subset_closedBall hz.1))
    dsimp only
    simp only [ConnectionVariation.covDerivAlong_def, (hw' _).fderiv_eq,
      (hw' _).eq_of_nhds, hw.fderiv_eq, hw.eq_of_nhds]
    exact hh
  refine ⟨p, r, q, hr, hr1, hq, hp, hmap, huc, hum, hVm, ?_, ?_⟩
  · intro i a
    let μ := volume.restrict (Metric.ball (0 : LoopPlane) r)
    let π : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := EuclideanSpace.proj a
    let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hi : Integrable (V i) μ := (hVm i).integrable
      (by simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ q by linarith only [hq]))
    apply puncture_weak_partial i (f := fun z => π (u z)) (h := fun z => π (V i z))
      (π.continuous.comp_continuousOn huc)
      (fun z hz => (π.contDiff.contDiffAt.comp z (hup hz)).contDiffWithinAt)
      (π.integrable_comp hi)
    intro z hz
    have hd := π.hasFDerivAt.comp z
      ((hup hz).differentiableAt (by simp)).hasFDerivAt
    change V i z a = fderiv ℝ (π ∘ u) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i)
    rw [hd.fderiv]
    rfl
  · intro η hη hηc hηs
    exact puncture_harmonic_variation g p huc hus htarget hq hB.le hκ hVm hpow hτ hη hηc hηs

end PoincareConjecture.M60
