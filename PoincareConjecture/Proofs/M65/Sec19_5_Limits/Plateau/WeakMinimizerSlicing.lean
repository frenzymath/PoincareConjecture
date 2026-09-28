import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerACL
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Restriction
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace PoincareConjecture

theorem m65L2_exists_slice_subsequence
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : Measure X} {nu : Measure Y} [SFinite mu] [SFinite nu]
    {u : ℕ → Lp ℝ 2 (mu.prod nu)} {u0 : Lp ℝ 2 (mu.prod nu)}
    (hconv : Tendsto u atTop (𝓝 u0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ x ∂mu,
      ∃ (hx : ∀ n, MemLp (fun y => u (σ n) (x, y)) 2 nu)
        (hx0 : MemLp (fun y => u0 (x, y)) 2 nu),
        Tendsto (fun n => (hx n).toLp (fun y => u (σ n) (x, y))) atTop
          (𝓝 (hx0.toLp (fun y => u0 (x, y)))) := by
  let err (n : ℕ) (x : X) := ∫ y, (u n (x, y) - u0 (x, y)) ^ 2 ∂nu
  have hsq (n : ℕ) : Integrable
      (fun p : X × Y => (u n p - u0 p) ^ 2) (mu.prod nu) :=
    ((Lp.memLp (u n)).sub (Lp.memLp u0)).integrable_sq
  have herr (n : ℕ) : Integrable (err n) mu := (hsq n).integral_prod_left
  have hnonneg (n : ℕ) (x : X) : 0 ≤ err n x :=
    integral_nonneg (fun _ => sq_nonneg _)
  let e (n : ℕ) : Lp ℝ 1 mu := (herr n).toL1 (err n)
  have hnorm (n : ℕ) : ‖e n‖ = ‖u n - u0‖ ^ 2 := by
    rw [L1.norm_eq_integral_norm]
    have heq : (∫ x, ‖e n x‖ ∂mu) = ∫ x, err n x ∂mu := by
      apply integral_congr_ae
      filter_upwards [(herr n).coeFn_toL1] with x hx
      rw [hx, Real.norm_eq_abs, abs_of_nonneg (hnonneg n x)]
    rw [heq, ← integral_prod _ (hsq n), Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) u0] with p hp
    simp only [hp, Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  have heconv : Tendsto e atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero, hnorm, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      ((hconv.sub (tendsto_const_nhds (x := u0))).norm.pow 2)
  obtain ⟨σ, hσ, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp heconv).exists_seq_tendsto_ae
  have herrpoint : ∀ᵐ x ∂mu, Tendsto (fun n => err (σ n) x) atTop (𝓝 0) := by
    filter_upwards [hpoint, ae_all_iff.mpr (fun n => (herr n).coeFn_toL1),
      Lp.coeFn_zero ℝ 1 mu] with x hx he hz
    rw [hz] at hx
    exact hx.congr (fun n => he (σ n))
  have hmem (v : Lp ℝ 2 (mu.prod nu)) :
      ∀ᵐ x ∂mu, MemLp (fun y => v (x, y)) 2 nu := by
    filter_upwards [(Lp.memLp v).integrable_sq.prod_right_ae] with x hx
    have hm : StronglyMeasurable (fun y => v (x, y)) :=
      (Lp.stronglyMeasurable v).comp_measurable measurable_prodMk_left
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hx
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [herrpoint, ae_all_iff.mpr (fun n => hmem (u n)), hmem u0]
    with x hx hu hu0
  refine ⟨fun n => hu (σ n), hu0, ?_⟩
  have hnormsq (n : ℕ) :
      ‖(hu (σ n)).toLp (fun y => u (σ n) (x, y)) -
        hu0.toLp (fun y => u0 (x, y))‖ ^ 2 = err (σ n) x := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hu (σ n)).toLp (fun y => u (σ n) (x, y)))
      (hu0.toLp (fun y => u0 (x, y))), (hu (σ n)).coeFn_toLp, hu0.coeFn_toLp]
      with y hsub hyn hy0
    simp only [hsub, Pi.sub_apply, hyn, hy0, Real.norm_eq_abs, sq_abs]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqconv := hx.congr (fun n => (hnormsq n).symm)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsqconv
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

theorem m65Product_AC_of_smooth_L2_graph
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [SFinite mu]
    {a b : ℝ} (hab : a < b) (f : ℕ → X → ℝ → ℝ)
    (hf : ∀ n x, ContDiff ℝ 1 (f n x))
    (u d : ℕ → Lp ℝ 2 (mu.prod (volume.restrict (Icc a b))))
    (u0 d0 : Lp ℝ 2 (mu.prod (volume.restrict (Icc a b))))
    (hu : ∀ n, u n =ᵐ[mu.prod (volume.restrict (Icc a b))]
      fun p => f n p.1 p.2)
    (hd : ∀ n, d n =ᵐ[mu.prod (volume.restrict (Icc a b))]
      fun p => deriv (f n p.1) p.2)
    (hu0 : Tendsto u atTop (𝓝 u0)) (hd0 : Tendsto d atTop (𝓝 d0)) :
    ∀ᵐ x ∂mu, ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      v =ᵐ[volume.restrict (Icc a b)] (fun y => u0 (x, y)) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        v t - v s = ∫ y in s..t, d0 (x, y) := by
  obtain ⟨σ, hσ, hU⟩ := m65L2_exists_slice_subsequence hu0
  obtain ⟨τ, hτ, hD⟩ :=
    m65L2_exists_slice_subsequence (hd0.comp hσ.tendsto_atTop)
  have hUf : ∀ᵐ x ∂mu, ∀ n, ∀ᵐ y ∂volume.restrict (Icc a b),
      u n (x, y) = f n x y :=
    ae_all_iff.mpr (fun n => Measure.ae_ae_of_ae_prod (hu n))
  have hDf : ∀ᵐ x ∂mu, ∀ n, ∀ᵐ y ∂volume.restrict (Icc a b),
      d n (x, y) = deriv (f n x) y :=
    ae_all_iff.mpr (fun n => Measure.ae_ae_of_ae_prod (hd n))
  filter_upwards [hU, hD, hUf, hDf] with x hUx hDx hUfx hDfx
  obtain ⟨hUn, hU0, hUconv⟩ := hUx
  obtain ⟨hDn, hD0, hDconv⟩ := hDx
  let U (n : ℕ) := (hUn (τ n)).toLp (fun y => u (σ (τ n)) (x, y))
  let D (n : ℕ) := (hDn n).toLp (fun y => d (σ (τ n)) (x, y))
  let U0 := hU0.toLp (fun y => u0 (x, y))
  let D0 := hD0.toLp (fun y => d0 (x, y))
  have hUactual (n : ℕ) : U n =ᵐ[volume.restrict (Icc a b)] f (σ (τ n)) x :=
    (hUn (τ n)).coeFn_toLp.trans (hUfx (σ (τ n)))
  have hDactual (n : ℕ) : D n =ᵐ[volume.restrict (Icc a b)] deriv (f (σ (τ n)) x) :=
    (hDn n).coeFn_toLp.trans (hDfx (σ (τ n)))
  obtain ⟨v, hvAC, hvAE, hvint⟩ := m65Interval_AC_of_smooth_L2_graph hab
    (fun n => f (σ (τ n)) x) (fun n => hf (σ (τ n)) x) U D U0 D0
    hUactual hDactual (hUconv.comp hτ.tendsto_atTop) hDconv
  refine ⟨v, hvAC, hvAE.trans hU0.coeFn_toLp, ?_⟩
  intro s hs t ht
  rw [hvint s hs t ht]
  apply intervalIntegral.integral_congr_ae_restrict
  exact ae_restrict_of_ae_restrict_of_subset
    ((uIoc_subset_uIcc).trans (uIcc_subset_Icc hs ht)) hD0.coeFn_toLp

end PoincareConjecture
