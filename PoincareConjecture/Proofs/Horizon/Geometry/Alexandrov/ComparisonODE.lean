import PoincareConjecture.Proofs.Horizon.Analysis.Convex.UpperSupport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Alexandrov

theorem ode_lower_comparison_of_approximate_upper_support
    {f L : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hL : ContDiff ℝ 2 L)
    (hode : ∀ t ∈ Ioo a b, deriv (deriv L) t = L t)
    (ha : L a ≤ f a) (hb : L b ≤ f b)
    (hsupport : ∀ t ∈ Ioo a b, ∀ ε : ℝ, 0 < ε →
      ∃ u : ℝ → ℝ, ContDiffAt ℝ 2 u t ∧ u t = f t ∧
        (∀ᶠ s in 𝓝 t, f s ≤ u s) ∧ deriv (deriv u) t ≤ f t + ε) :
    ∀ t ∈ Icc a b, L t ≤ f t := by
  intro t ht
  by_contra hnot
  let F : ℝ → ℝ := fun s => f s - L s
  have hFc : ContinuousOn F (Icc a b) := hf.sub hL.continuous.continuousOn
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨t, ht⟩ hFc
  have hFx : F x < 0 := (hmin ht).trans_lt (sub_neg.mpr (lt_of_not_ge hnot))
  have hax : a < x := lt_of_le_of_ne hx.1 (by
    intro h
    have hFa : 0 ≤ F a := sub_nonneg.mpr ha
    rw [← h] at hFx
    exact (not_lt_of_ge hFa) hFx)
  have hxb : x < b := lt_of_le_of_ne hx.2 (by
    intro h
    have hFb : 0 ≤ F b := sub_nonneg.mpr hb
    rw [h] at hFx
    exact (not_lt_of_ge hFb) hFx)
  obtain ⟨u, hu, htouch, hupper, hsecond⟩ :=
    hsupport x ⟨hax, hxb⟩ (-F x / 2) (by linarith)
  have humin : IsLocalMin (fun s => u s - L s) x := by
    filter_upwards [hmin.isLocalMin (Icc_mem_nhds hax hxb), hupper] with s hs hsu
    change f x - L x ≤ f s - L s at hs
    rw [htouch]
    linarith
  have hnonneg := Poincare.Analysis.nonneg_second_deriv_of_local_min
    (hu.sub hL.contDiffAt) humin
  have hfirst : deriv (fun s => u s - L s) =ᶠ[𝓝 x]
      (fun s => deriv u s - deriv L s) := by
    filter_upwards [hu.eventually (by norm_num)] with s hs
    exact deriv_fun_sub (hs.differentiableAt (by norm_num))
      (hL.differentiable (by norm_num) s)
  have hud : DifferentiableAt ℝ (deriv u) x :=
    (hu.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hLd : DifferentiableAt ℝ (deriv L) x :=
    (hL.contDiffAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hfirst.deriv_eq, deriv_fun_sub hud hLd, hode x ⟨hax, hxb⟩] at hnonneg
  dsimp [F] at hsecond hFx
  linarith

private theorem hyperbolic_combination_hasDerivAt (A B t : ℝ) :
    HasDerivAt (fun s => A * Real.cosh s + B * Real.sinh s)
      (A * Real.sinh t + B * Real.cosh t) t :=
  ((Real.hasDerivAt_cosh t).const_mul A).add
    ((Real.hasDerivAt_sinh t).const_mul B)

private theorem hyperbolic_combination_second_deriv (A B t : ℝ) :
    deriv (deriv (fun s => A * Real.cosh s + B * Real.sinh s)) t =
      A * Real.cosh t + B * Real.sinh t := by
  have hfirst : deriv (fun s => A * Real.cosh s + B * Real.sinh s) =
      (fun s => A * Real.sinh s + B * Real.cosh s) := by
    funext s
    exact (hyperbolic_combination_hasDerivAt A B s).deriv
  rw [hfirst]
  exact (((Real.hasDerivAt_sinh t).const_mul A).add
    ((Real.hasDerivAt_cosh t).const_mul B)).deriv

theorem hyperbolic_upper_comparison_of_approximate_upper_support
    {f u : ℝ → ℝ} {b v₀ : ℝ} (hb : 0 < b)
    (hf : ContinuousOn f (Icc 0 b))
    (htouch : u 0 = f 0) (hupper : ∀ᶠ s in 𝓝 0, f s ≤ u s)
    (hu : HasDerivAt u v₀ 0)
    (hsupport : ∀ t ∈ Ioo 0 b, ∀ ε : ℝ, 0 < ε →
      ∃ v : ℝ → ℝ, ContDiffAt ℝ 2 v t ∧ v t = f t ∧
        (∀ᶠ s in 𝓝 t, f s ≤ v s) ∧ deriv (deriv v) t ≤ f t + ε) :
    f b ≤ f 0 * Real.cosh b + v₀ * Real.sinh b := by
  let B : ℝ := (f b - f 0 * Real.cosh b) / Real.sinh b
  let L : ℝ → ℝ := fun t => f 0 * Real.cosh t + B * Real.sinh t
  have hsinh : 0 < Real.sinh b := Real.sinh_pos_iff.mpr hb
  have hL0 : L 0 = f 0 := by simp [L]
  have hLb : L b = f b := by
    dsimp [L, B]
    rw [div_mul_cancel₀ _ hsinh.ne']
    ring
  have hLle : ∀ t ∈ Icc 0 b, L t ≤ f t :=
    ode_lower_comparison_of_approximate_upper_support hf (by dsimp [L]; fun_prop)
      (fun t _ => hyperbolic_combination_second_deriv (f 0) B t)
      hL0.le hLb.le hsupport
  have hLd : HasDerivAt L B 0 := by
    simpa [L] using hyperbolic_combination_hasDerivAt (f 0) B 0
  have hBle : B ≤ v₀ := by
    apply le_of_tendsto_of_tendsto
      (hLd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0))
      (hu.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0))
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds,
      hupper.filter_mono nhdsWithin_le_nhds] with t ht htb htu
    have htpos : 0 < t := ht
    simp only [slope_def_field, hL0, htouch]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right ((hLle t ⟨htpos.le, htb.le⟩).trans htu) _)
      (sub_nonneg.mpr htpos.le)
  have h := (div_le_iff₀ hsinh).mp hBle
  linarith

end Poincare.Alexandrov
