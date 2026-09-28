import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyApproximation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyFourier
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Complex
open scoped Topology SchwartzMap ContDiff InnerProductSpace

namespace PoincareConjecture.M65Branch




private theorem integral_test_mul_L2_eq (φ : ℂ → ℂ) (hφ : MemLp φ 2 volume)
    (d : Lp ℂ 2 (volume : Measure ℂ)) :
    (∫ z, φ z * d z) = inner ℂ (star (hφ.toLp φ)) d := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (hφ.toLp φ), hφ.coeFn_toLp] with z hz hφz
  simp only [hz, Pi.star_apply, hφz, RCLike.inner_apply', starRingEnd_apply, star_star]




private theorem weak_derivative_of_cauchy_approximation
    (f : ℕ → 𝓢(ℂ, ℂ)) (hs : ∀ n, HasCompactSupport (f n : ℂ → ℂ))
    {g : ℂ → ℂ} {B : ℝ} (hb : ∀ n z, ‖cauchyOperator (f n) z‖ ≤ B)
    (hconv : TendstoUniformly (fun n => cauchyOperator (f n)) g atTop)
    (v : ℂ) (d : ℕ → Lp ℂ 2 (volume : Measure ℂ))
    (dlim : Lp ℂ 2 (volume : Measure ℂ))
    (hd : ∀ n, (fun z => fderiv ℝ (cauchyOperator (f n)) z v) =ᵐ[volume] d n)
    (hdconv : Tendsto d atTop (𝓝 dlim))
    (φ : ℂ → ℂ) (hφd : ContDiff ℝ 1 φ) (hφ : HasCompactSupport φ) :
    (∫ z, φ z * dlim z) = -∫ z, fderiv ℝ φ z v * g z := by
  have hC (n : ℕ) : ContDiff ℝ 1 (cauchyOperator (f n)) :=
    contDiff_cauchyOperator ((f n).smooth 1) (hs n)
  have hDφ : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDφi : Integrable (fun z => ‖fderiv ℝ φ z v‖) :=
    (hDφ.integrable_of_hasCompactSupport (hφ.fderiv_apply ℝ v)).norm
  have hright : Tendsto (fun n => ∫ z, fderiv ℝ φ z v * cauchyOperator (f n) z)
      atTop (𝓝 (∫ z, fderiv ℝ φ z v * g z)) := by
    apply tendsto_integral_of_dominated_convergence (fun z => ‖fderiv ℝ φ z v‖ * B)
    · intro n
      exact (hDφ.mul (hC n).continuous).aestronglyMeasurable
    · exact hDφi.mul_const B
    · intro n
      filter_upwards [] with z
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb n z) (norm_nonneg _)
    · filter_upwards [] with z
      exact tendsto_const_nhds.mul (hconv.tendsto_at z)
  have hleft : Tendsto (fun n => ∫ z, φ z * d n z)
      atTop (𝓝 (∫ z, φ z * dlim z)) := by
    simp_rw [integral_test_mul_L2_eq φ (hφd.continuous.memLp_of_hasCompactSupport hφ)]
    exact tendsto_const_nhds.inner hdconv
  have hid (n : ℕ) : (∫ z, φ z * d n z) =
      -∫ z, fderiv ℝ φ z v * cauchyOperator (f n) z := by
    have hCD : Continuous (fun z => fderiv ℝ (cauchyOperator (f n)) z v) :=
      ((hC n).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h1 : Integrable (fun z => fderiv ℝ φ z v * cauchyOperator (f n) z) :=
      (hDφ.mul (hC n).continuous).integrable_of_hasCompactSupport
        (hφ.fderiv_apply ℝ v).mul_right
    have h2 : Integrable (fun z => φ z * fderiv ℝ (cauchyOperator (f n)) z v) :=
      (hφd.continuous.mul hCD).integrable_of_hasCompactSupport hφ.mul_right
    have h3 : Integrable (fun z => φ z * cauchyOperator (f n) z) :=
      (hφd.continuous.mul (hC n).continuous).integrable_of_hasCompactSupport hφ.mul_right
    calc
      _ = ∫ z, φ z * fderiv ℝ (cauchyOperator (f n)) z v := by
        apply integral_congr_ae
        filter_upwards [hd n] with z hz
        rw [hz]
      _ = _ := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
        (fun z _ => hφd.differentiable one_ne_zero z)
        (fun z _ => (hC n).differentiable one_ne_zero z)
  exact tendsto_nhds_unique hleft (hright.neg.congr fun n => (hid n).symm)





theorem cauchyOperator_weak_derivatives_C1 {h : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : MemLp h 2 volume)
    (hs : Function.support h ⊆ Metric.closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖h z‖ ≤ B) :
    let u := hh.toLp h
    ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, φ z * (u + beurlingL2 u) z) =
        -∫ z, fderiv ℝ φ z 1 * cauchyOperator h z ∧
      (∫ z, φ z * (I • (beurlingL2 u - u)) z) =
        -∫ z, fderiv ℝ φ z I * cauchyOperator h z := by
  obtain ⟨f, hfs, _, hCb, hu, hC⟩ :=
    exists_cauchy_schwartz_approximation hR hB hh hs hb
  let un (n : ℕ) := (f n).toLp 2 volume
  let u := hh.toLp h
  have hBconv : Tendsto (fun n => beurlingL2 (un n)) atTop (𝓝 (beurlingL2 u)) :=
    beurlingL2.continuous.tendsto u |>.comp hu
  dsimp only
  intro φ hφd hφ
  constructor
  · apply weak_derivative_of_cauchy_approximation f hfs hCb hC 1
      (fun n => un n + beurlingL2 (un n)) (u + beurlingL2 u) ?_
      (hu.add hBconv) φ hφd hφ
    intro n
    filter_upwards [(fderiv_cauchyOperator_beurling_ae (f n) (hfs n)).1,
      Lp.coeFn_add (un n) (beurlingL2 (un n)), (f n).coeFn_toLp 2 volume] with z hz ha hf
    simpa only [ha, Pi.add_apply, un, hf] using hz
  · apply weak_derivative_of_cauchy_approximation f hfs hCb hC I
      (fun n => I • (beurlingL2 (un n) - un n)) (I • (beurlingL2 u - u)) ?_
      ((hBconv.sub hu).const_smul I) φ hφd hφ
    intro n
    filter_upwards [(fderiv_cauchyOperator_beurling_ae (f n) (hfs n)).2,
      Lp.coeFn_smul I (beurlingL2 (un n) - un n),
      Lp.coeFn_sub (beurlingL2 (un n)) (un n), (f n).coeFn_toLp 2 volume] with z hz hm hs hf
    simpa only [hm, Pi.smul_apply, hs, Pi.sub_apply, smul_eq_mul, un, hf] using hz




theorem cauchyOperator_weak_derivatives {h : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : MemLp h 2 volume)
    (hs : Function.support h ⊆ Metric.closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖h z‖ ≤ B) :
    let u := hh.toLp h
    ∀ φ : 𝓢(ℂ, ℂ), HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z * (u + beurlingL2 u) z) =
        -∫ z, fderiv ℝ φ z 1 * cauchyOperator h z ∧
      (∫ z, φ z * (I • (beurlingL2 u - u)) z) =
        -∫ z, fderiv ℝ φ z I * cauchyOperator h z := by
  dsimp only
  intro φ hφ
  exact cauchyOperator_weak_derivatives_C1 hR hB hh hs hb φ (φ.smooth 1) hφ

end PoincareConjecture.M65Branch
