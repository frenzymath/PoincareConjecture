import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.WeakBound
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal Convolution

namespace Poincare.Analysis.Sobolev.BoundaryApproximation

open DifferenceQuotient

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem small_steps : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 ∧ |h| ≤ 1 := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with h hh hb
  exact ⟨hh, le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hb)⟩

private theorem smooth_local_convergence {v : E → ℝ} (hv : ContDiff ℝ 1 v)
    (k : Fin d) {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) :
    Tendsto (fun h : ℝ => eLpNorm
      (fun x => diffQuot k h v x - fderiv ℝ v x (EuclideanSpace.single k 1))
      2 (volume.restrict V)) (𝓝[≠] 0) (𝓝 0) := by
  let dv : E → ℝ := fun x => fderiv ℝ v x (EuclideanSpace.single k 1)
  have hdcont : Continuous dv :=
    (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨R, hVR⟩ := hVc.isBounded.subset_closedBall (0 : E)
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : E) (R + 1)).exists_bound_of_continuousOn
    (hv.continuous_fderiv one_ne_zero).continuousOn
  let C : ℝ := max C₀ 0
  have hC (x : E) (hx : x ∈ Metric.closedBall 0 (R + 1)) : ‖fderiv ℝ v x‖ ≤ C :=
    (hC₀ x hx).trans (le_max_left _ _)
  have hxn (x : E) (hx : x ∈ V) : ‖x‖ ≤ R := by
    simpa using hVR (subset_closure hx)
  have hxb (x : E) (hx : x ∈ V) : x ∈ Metric.closedBall 0 (R + 1) := by
    simpa using (hxn x hx).trans (by linarith : R ≤ R + 1)
  have hbound (h : ℝ) (hh : h ≠ 0) (hh1 : |h| ≤ 1) (x : E) (hx : x ∈ V) :
      ‖diffQuot k h v x - dv x‖ ≤ 2 * C := by
    have hyb : x + h • EuclideanSpace.single k 1 ∈ Metric.closedBall (0 : E) (R + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        _ ≤ ‖x‖ + ‖h • EuclideanSpace.single k (1 : ℝ)‖ := norm_add_le _ _
        _ = ‖x‖ + |h| := by simp [norm_smul, Real.norm_eq_abs]
        _ ≤ R + 1 := add_le_add (hxn x hx) hh1
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hv.differentiable_one y) hC (convex_closedBall (0 : E) (R + 1))
      (hxb x hx) hyb
    have hdq : ‖diffQuot k h v x‖ ≤ C := by
      rw [diffQuot_apply_of_ne k hh, norm_div, Real.norm_eq_abs]
      apply (div_le_iff₀ (abs_pos.mpr hh)).mpr
      simpa [norm_smul, Real.norm_eq_abs] using hmv
    have hdv : ‖dv x‖ ≤ C := by
      have hop := (fderiv ℝ v x).le_opNorm (EuclideanSpace.single k (1 : ℝ))
      have hop' : ‖dv x‖ ≤ ‖fderiv ℝ v x‖ := by simpa [dv] using hop
      exact hop'.trans (hC x (hxb x hx))
    exact (norm_sub_le _ _).trans ((add_le_add hdq hdv).trans_eq (by ring))
  have hvol : (volume : Measure E) V < ∞ :=
    (measure_mono subset_closure).trans_lt hVc.measure_lt_top
  let : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hvol⟩
  have hint : Tendsto
      (fun h : ℝ => ∫⁻ x, (‖diffQuot k h v x - dv x‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume.restrict V)) (𝓝[≠] 0) (𝓝 0) := by
    have ht := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := volume.restrict V) (l := 𝓝[≠] (0 : ℝ))
      (F := fun h x => (‖diffQuot k h v x - dv x‖ₑ : ℝ≥0∞) ^ 2)
      (f := fun _ => (0 : ℝ≥0∞)) (fun _ => (ENNReal.ofReal (2 * C)) ^ 2)
      (Eventually.of_forall fun h => by
        have hm : Measurable (fun x => (‖diffQuot k h v x - dv x‖ₑ : ℝ≥0∞)) :=
          ((continuous_diffQuot_of_continuous k h hv.continuous).sub hdcont).measurable.enorm
        exact (hm.pow_const 2).aemeasurable) ?_ ?_ ?_
    · simpa using ht
    · filter_upwards [small_steps] with h hh
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      apply pow_le_pow_left' _ 2
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbound h hh.1 hh.2 x hx)
    · simp only [lintegral_const]
      finiteness
    · exact Eventually.of_forall fun x => by
        have hp : Tendsto (fun h => (‖diffQuot k h v x - dv x‖ₑ : ℝ≥0∞))
            (𝓝[≠] 0) (𝓝 0) := by
          simpa [dv] using ((tendsto_diffQuot_of_contDiff hv k x).sub_const
            (fderiv ℝ v x (EuclideanSpace.single k 1))).enorm
        simpa only [Function.comp_def, zero_pow (by norm_num : 2 ≠ 0)] using
          ((ENNReal.continuous_pow 2).tendsto 0).comp hp
  have hr := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp hint
  convert! hr using 1
  · funext h
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num [dv, ENNReal.rpow_natCast]
  · norm_num

private theorem memLp_differenceQuotient {u : E → ℝ} (hu : MemLp u 2 volume)
    (k : Fin d) (h : ℝ) : MemLp (diffQuot k h u) 2 volume := by
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h]
    exact MemLp.zero
  · rw [diffQuot_eq_translate_sub_div k hh]
    simpa only [div_eq_mul_inv, Pi.sub_apply] using
      ((memLp_translate k h hu).sub hu).mul_const h⁻¹

private theorem weakPartial_sub {u v g q : E → ℝ} (k : Fin d)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hg : MemLp g 2 volume) (hq : MemLp q 2 volume)
    (hgu : Weak.HasWeakPartialDeriv k g u univ)
    (hqv : Weak.HasWeakPartialDeriv k q v univ) :
    Weak.HasWeakPartialDeriv k (g - q) (u - v) univ := by
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hDLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single k 1)) 2 volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)
  have h1 := hgu φ hφ hc hs
  have h2 := hqv φ hφ hc hs
  simp only [Measure.restrict_univ] at h1 h2 ⊢
  simp only [Pi.sub_apply, sub_mul]
  have hs1 := integral_sub (hu.integrable_mul hDLp) (hv.integrable_mul hDLp)
  have hs2 := integral_sub (hg.integrable_mul hφLp) (hq.integrable_mul hφLp)
  simp only [Pi.mul_apply] at hs1 hs2
  rw [hs1, hs2, h1, h2]
  ring

private theorem mollify_comm {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) :
    mollifyEps hε u =
      u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps hε := by
  funext x
  unfold mollifyEps
  rw [convolution_lsmul, convolution_lsmul_swap]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by simp [smul_eq_mul, mul_comm]



theorem tendsto_eLpNorm_diffQuot_sub_weakPartial
    {u g : E → ℝ} (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (k : Fin d) (hweak : Weak.HasWeakPartialDeriv k g u Set.univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) :
    Tendsto (fun h : ℝ => eLpNorm (fun x => diffQuot k h u x - g x)
      2 (volume.restrict V)) (𝓝[≠] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ∞
  · simp [hεtop]
  let a : ℝ≥0∞ := ENNReal.ofReal (ε.toReal / 3)
  have ha : 0 < a := ENNReal.ofReal_pos.mpr
    (div_pos (ENNReal.toReal_pos hε.ne' hεtop) (by norm_num))
  obtain ⟨δ, hδ, happ⟩ := Euclidean.exists_eLpNorm_convolution_mollifierEps_sub_le
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hg ha
  let v : E → ℝ := mollifyEps hδ u
  let q : E → ℝ := mollifyEps hδ g
  have happrox : eLpNorm (q - g) 2 volume ≤ a := by
    change eLpNorm (fun x => q x - g x) 2 volume ≤ a
    simpa only [q, mollify_comm hδ, Pi.sub_apply] using happ δ hδ le_rfl
  have huLoc := hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgLoc := hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hvs : ContDiff ℝ (⊤ : ℕ∞) v := mollifyEps_contDiff hδ huLoc
  have hqs : ContDiff ℝ (⊤ : ℕ∞) q := mollifyEps_contDiff hδ hgLoc
  have hv : MemLp v 2 volume :=
    ⟨hvs.continuous.aestronglyMeasurable, (eLpNorm_mollifyEps_le hδ hu).trans_lt hu.2⟩
  have hq : MemLp q 2 volume :=
    ⟨hqs.continuous.aestronglyMeasurable, (eLpNorm_mollifyEps_le hδ hg).trans_lt hg.2⟩
  have hderiv (x : E) : fderiv ℝ v x (EuclideanSpace.single k 1) = q x :=
    mollifyEps_partial_eq_mollifyEps_weakPartial hδ huLoc hweak x
  have hqweak : Weak.HasWeakPartialDeriv k q v univ := by
    have heq : (fun x => fderiv ℝ v x (EuclideanSpace.single k 1)) = q := funext hderiv
    rw [← heq]
    exact Weak.HasWeakPartialDeriv.of_contDiff isOpen_univ (hvs.of_le (by norm_cast))
  have hsub := weakPartial_sub k hu hv hg hq hweak hqweak
  have hsmooth : Tendsto
      (fun h : ℝ => eLpNorm (fun x => diffQuot k h v x - q x) 2 (volume.restrict V))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hderiv] using smooth_local_convergence (hvs.of_le (by norm_cast)) k hV hVc
  filter_upwards [small_steps, ENNReal.tendsto_nhds_zero.mp hsmooth a ha] with h hh hmid
  have hfirst : eLpNorm (diffQuot k h (u - v)) 2 (volume.restrict V) ≤ a := by
    have hb := eLpNorm_diffQuot_le_eLpNorm_weakPartial (hu.sub hv) (hg.sub hq) k hsub
      isOpen_univ hV hVc (show (0 : ℝ) < 1 by norm_num) (subset_univ _) hh.1 hh.2
    simp only [Measure.restrict_univ] at hb
    exact hb.trans (by simpa only [eLpNorm_sub_comm] using happrox)
  have hthird : eLpNorm (q - g) 2 (volume.restrict V) ≤ a :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans happrox
  have hA := (memLp_differenceQuotient (hu.sub hv) k h).restrict V
  have hB := ((memLp_differenceQuotient hv k h).restrict V).sub (hq.restrict V)
  have hC := (hq.sub hg).restrict V
  have hsum : a + a + a = ε := by
    dsimp [a]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    convert ENNReal.ofReal_toReal hεtop using 1
    congr 1
    ring
  calc
    _ = eLpNorm (fun x =>
        (diffQuot k h (u - v) x + (diffQuot k h v x - q x)) + (q x - g x))
        2 (volume.restrict V) := by
      congr 1
      funext x
      simp only [diffQuot_sub, Pi.sub_apply]
      ring
    _ ≤ (eLpNorm (diffQuot k h (u - v)) 2 (volume.restrict V) +
          eLpNorm (fun x => diffQuot k h v x - q x) 2 (volume.restrict V)) +
        eLpNorm (q - g) 2 (volume.restrict V) :=
      (eLpNorm_add_le (hA.add hB).1 hC.1 (by norm_num)).trans
        (add_le_add (eLpNorm_add_le hA.1 hB.1 (by norm_num)) le_rfl)
    _ ≤ a + a + a := add_le_add (add_le_add hfirst hmid) hthird
    _ = ε := hsum

end Poincare.Analysis.Sobolev.BoundaryApproximation
