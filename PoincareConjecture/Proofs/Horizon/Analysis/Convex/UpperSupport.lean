import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Analysis

theorem nonneg_second_deriv_of_local_min {u : ℝ → ℝ} {x : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hmin : IsLocalMin u x) :
    0 ≤ deriv (deriv u) x := by
  by_contra hnonneg
  have hneg : deriv (deriv u) x < 0 := lt_of_not_ge hnonneg
  have hc : ContinuousAt (deriv (deriv u)) x :=
    ((hu.derivWithin (m := 1) (by norm_num)).derivWithin
      (m := 0) (by norm_num)).continuousAt
  have hev : ∀ᶠ y in 𝓝 x,
      u x ≤ u y ∧ ContDiffAt ℝ 2 u y ∧ deriv (deriv u) y < 0 := by
    filter_upwards [hmin, hu.eventually (by norm_num),
      hc.eventually_lt continuousAt_const hneg] with y h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hconc : StrictConcaveOn ℝ (Metric.ball x r) u := by
    apply strictConcaveOn_of_deriv2_neg (convex_ball x r)
    · exact fun y hy => (hball hy).2.1.continuousAt.continuousWithinAt
    · intro y hy
      have hball_eq : interior (Metric.ball x r) = Metric.ball x r :=
        Metric.isOpen_ball.interior_eq
      exact (hball (Metric.mem_ball.mp (hball_eq ▸ hy))).2.2
  have hxy : x < x + r / 2 := by linarith
  have hy : x + r / 2 ∈ Metric.ball x r := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [show x + r / 2 - x = r / 2 by ring, abs_of_pos (by positivity)]
    linarith
  have hslope := hconc.slope_lt_deriv (Metric.mem_ball_self hr) hy hxy
    (hu.differentiableAt (by norm_num))
  rw [hmin.deriv_eq_zero, slope_def_field] at hslope
  have hpos : 0 ≤ (u (x + r / 2) - u x) / (x + r / 2 - x) :=
    div_nonneg (sub_nonneg.mpr (hball hy).1) (sub_nonneg.mpr hxy.le)
  exact (not_lt_of_ge hpos) hslope

theorem concaveOn_of_approximate_upper_support {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∀ ε : ℝ, 0 < ε →
      ∃ u : ℝ → ℝ, ContDiffAt ℝ 2 u x ∧ u x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ u y) ∧ deriv (deriv u) x ≤ ε) :
    ConcaveOn ℝ (Icc a b) f := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc a b)
  intro x y z hx hz hxy hyz
  have hxz : x < z := hxy.trans hyz
  let L : ℝ → ℝ := fun t => f x + (t - x) * ((f z - f x) / (z - x))
  have hLx : L x = f x := by simp [L]
  have hLz : L z = f z := by
    dsimp [L]
    field_simp [sub_ne_zero.mpr hxz.ne']
    ring
  have hchord : L y ≤ f y := by
    by_contra hnot
    have hgap : 0 < L y - f y := sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt hgap ((y - x) * (z - y))
    let P : ℝ → ℝ := fun t => -L t + ε * (t - x) * (z - t)
    let F : ℝ → ℝ := fun t => f t + P t
    have hPc : ContDiff ℝ 2 P := by dsimp [P, L]; fun_prop
    have hFc : ContinuousOn F (Icc x z) :=
      (hf.mono (Icc_subset_Icc hx.1 hz.2)).add hPc.continuous.continuousOn
    obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr hxz.le) hFc
    have hFy : F y < 0 := by dsimp [F, P]; nlinarith [hsmall]
    have hFt : F t < 0 := (hmin ⟨hxy.le, hyz.le⟩).trans_lt hFy
    have hFx : F x = 0 := by simp [F, P, hLx]
    have hFz : F z = 0 := by simp [F, P, hLz]
    have hxt : x < t := lt_of_le_of_ne ht.1 (by
      intro h; rw [← h, hFx] at hFt; exact lt_irrefl _ hFt)
    have htz : t < z := lt_of_le_of_ne ht.2 (by
      intro h; rw [h, hFz] at hFt; exact lt_irrefl _ hFt)
    obtain ⟨u, hu, htouch, hupper, hsecond⟩ :=
      hsupport t ⟨hx.1.trans_lt hxt, htz.trans_le hz.2⟩ ε hε
    have humin : IsLocalMin (fun s => u s + P s) t := by
      filter_upwards [hmin.isLocalMin (Icc_mem_nhds hxt htz), hupper] with s hs hsu
      change f t + P t ≤ f s + P s at hs
      rw [htouch]
      linarith
    have hnonneg := nonneg_second_deriv_of_local_min (hu.add hPc.contDiffAt) humin
    let P' : ℝ → ℝ := fun s => -((f z - f x) / (z - x)) + ε * (z + x - 2 * s)
    have hPd (s : ℝ) : HasDerivAt P (P' s) s := by
      dsimp [P, P', L]
      convert (((hasDerivAt_const s (f x)).add
        (((hasDerivAt_id s).sub_const x).mul_const ((f z - f x) / (z - x)))).neg).add
        ((((hasDerivAt_id s).sub_const x).const_mul ε).mul
          ((hasDerivAt_const s z).sub (hasDerivAt_id s))) using 1 <;>
        first | rfl | (simp only [Pi.sub_apply, id_eq]; ring)
    have hPdd : HasDerivAt P' (-2 * ε) t := by
      dsimp [P']
      convert (hasDerivAt_const t (-((f z - f x) / (z - x)))).add
        (((hasDerivAt_const t (z + x)).sub
          ((hasDerivAt_id t).const_mul 2)).const_mul ε) using 1 <;>
        first | rfl | ring
    have hfirst : deriv (fun s => u s + P s) =ᶠ[𝓝 t]
        (fun s => deriv u s + P' s) := by
      filter_upwards [hu.eventually (by norm_num)] with s hs
      rw [deriv_fun_add (hs.differentiableAt (by norm_num)) (hPd s).differentiableAt,
        (hPd s).deriv]
    have hud : DifferentiableAt ℝ (deriv u) t :=
      (hu.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [hfirst.deriv_eq, deriv_fun_add hud hPdd.differentiableAt, hPdd.deriv] at hnonneg
    linarith
  rw [div_le_div_iff₀ (sub_pos.mpr hyz) (sub_pos.mpr hxy)]
  have hchord' : (f z - f x) * (y - x) ≤ (f y - f x) * (z - x) := by
    have h : (y - x) * ((f z - f x) / (z - x)) ≤ f y - f x := by
      dsimp [L] at hchord
      linarith
    have hh := (mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hxz.le))
    field_simp at hh
    nlinarith
  nlinarith

theorem second_deriv_sub_quadratic {u : ℝ → ℝ} {x : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (C : ℝ) :
    deriv (deriv (fun t => u t - C * t ^ 2)) x = deriv (deriv u) x - 2 * C := by
  have hq (t : ℝ) : HasDerivAt (fun s : ℝ => C * s ^ 2) (2 * C * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul C using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hfirst : deriv (fun t => u t - C * t ^ 2) =ᶠ[𝓝 x]
      (fun t => deriv u t - 2 * C * t) := by
    filter_upwards [hu.eventually (by norm_num)] with t ht
    rw [deriv_fun_sub (ht.differentiableAt (by norm_num)) (hq t).differentiableAt,
      (hq t).deriv]
  have hud : DifferentiableAt ℝ (deriv u) x :=
    (hu.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hfirst.deriv_eq, deriv_fun_sub hud (by fun_prop)]
  simp

theorem concaveOn_sub_quadratic_of_approximate_upper_support
    {f : ℝ → ℝ} {a b C : ℝ} (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∀ ε : ℝ, 0 < ε →
      ∃ u : ℝ → ℝ, ContDiffAt ℝ 2 u x ∧ u x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ u y) ∧ deriv (deriv u) x ≤ 2 * C + ε) :
    ConcaveOn ℝ (Icc a b) (fun t => f t - C * t ^ 2) := by
  apply concaveOn_of_approximate_upper_support (hf.sub (by fun_prop))
  intro x hx ε hε
  obtain ⟨u, hu, ht, hb, hd⟩ := hsupport x hx ε hε
  refine ⟨fun t => u t - C * t ^ 2, hu.sub (by fun_prop), by simp only [Pi.sub_apply, ht],
    ?_, ?_⟩
  · exact hb.mono fun y hy => sub_le_sub_right hy _
  · rw [second_deriv_sub_quadratic hu]
    linarith

theorem le_affine_of_concaveOn_of_upper_support
    {f u : ℝ → ℝ} {a b q : ℝ} (hab : a < b)
    (hf : ConcaveOn ℝ (Icc a b) f) (htouch : u a = f a)
    (hupper : ∀ᶠ y in 𝓝 a, f y ≤ u y) (hu : HasDerivAt u q a) :
    f b ≤ f a + q * (b - a) := by
  have hlimit := hu.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)
  have hle : slope f a b ≤ q := by
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds,
      hupper.filter_mono nhdsWithin_le_nhds] with y hy hyb hyu
    have hya : a < y := hy
    have hsl := hf.slope_anti ⟨le_rfl, hab.le⟩
      (show y ∈ Icc a b \ {a} from ⟨⟨hya.le, hyb.le⟩, ne_of_gt hya⟩)
      (show b ∈ Icc a b \ {a} from ⟨⟨hab.le, le_rfl⟩, ne_of_gt hab⟩) hyb.le
    apply hsl.trans
    simp only [slope_def_field, ← htouch]
    exact div_le_div_of_nonneg_right (sub_le_sub_right hyu _) (sub_nonneg.mpr hya.le)
  rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hab)] at hle
  linarith

theorem two_parameter_chord_lower_bound
    {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (haxis₁ : ∀ t ∈ Icc 0 b,
      ConcaveOn ℝ (Icc 0 a) (fun s => F s t - s ^ 2))
    (haxis₂ : ∀ s ∈ Icc 0 a,
      ConcaveOn ℝ (Icc 0 b) (fun t => F s t - t ^ 2))
    (hzero₁ : ∀ s ∈ Icc 0 a, F s 0 = s ^ 2)
    (hzero₂ : ∀ t ∈ Icc 0 b, F 0 t = t ^ 2) :
    ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 b,
      F s t ≥ s ^ 2 + t ^ 2 -
        2 * s * t * ((a ^ 2 + b ^ 2 - F a b) / (2 * a * b)) := by
  intro s hs t ht
  have hst : 0 ≤ s / a := div_nonneg hs.1 ha.le
  have hsa_eq : s / a * a = s := by field_simp
  have htb_eq : t / b * b = t := by field_simp
  have htb : t / b ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg ht.1 hb.le
    · simpa using (div_le_iff₀ hb).2 (by simpa using ht.2)
  have hsa : s / a ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hs.1 ha.le
    · simpa using (div_le_iff₀ ha).2 (by simpa using hs.2)
  have hconc_s := (haxis₁ t ht).2
    (show (0 : ℝ) ∈ Icc 0 a by exact ⟨le_rfl, ha.le⟩)
    (show a ∈ Icc 0 a by exact ⟨ha.le, le_rfl⟩)
    (show 0 ≤ 1 - s / a by linarith [hsa.2])
    (show 0 ≤ s / a by exact div_nonneg hs.1 ha.le) (by ring)
  have hFa : F a t ≥ t ^ 2 + a ^ 2 + (t / b) * (F a b - a ^ 2 - b ^ 2) := by
    have hconc_t := (haxis₂ a (show a ∈ Icc 0 a by exact ⟨ha.le, le_rfl⟩)).2
      (show (0 : ℝ) ∈ Icc 0 b by exact ⟨le_rfl, hb.le⟩)
      (show b ∈ Icc 0 b by exact ⟨hb.le, le_rfl⟩)
      (show 0 ≤ 1 - t / b by linarith [htb.2])
      (show 0 ≤ t / b by exact div_nonneg ht.1 hb.le) (by ring)
    simp [smul_eq_mul, htb_eq, hzero₁ a ⟨ha.le, le_rfl⟩] at hconc_t
    nlinarith [hconc_t]
  simp [smul_eq_mul, hsa_eq, hzero₂ t ht] at hconc_s
  have hsineq : s ^ 2 + t ^ 2 + (s / a) * (F a t - a ^ 2 - t ^ 2) ≤ F s t := by
    nlinarith [hconc_s]
  have hfa' : t ^ 2 + a ^ 2 + (t / b) * (F a b - a ^ 2 - b ^ 2) - a ^ 2 - t ^ 2
      ≤ F a t - a ^ 2 - t ^ 2 := by
    nlinarith [hFa]
  have hmul := mul_le_mul_of_nonneg_left hfa' hst
  have hfinal : s ^ 2 + t ^ 2 + (s / a) * (t / b) *
      (F a b - a ^ 2 - b ^ 2) ≤ F s t := by
    nlinarith [hsineq, hmul]
  have hid : s ^ 2 + t ^ 2 + (s / a) * (t / b) *
      (F a b - a ^ 2 - b ^ 2) =
      s ^ 2 + t ^ 2 - 2 * s * t * ((a ^ 2 + b ^ 2 - F a b) / (2 * a * b)) := by
    field_simp [ha.ne', hb.ne']
    ring
  rw [← hid]
  exact hfinal

end Poincare.Analysis
