


import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod









set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace Poincare.Analysis

private theorem signs_of_strictMonoOn {δ x : ℝ} {f : ℝ → ℝ}
    (hδ : 0 < δ) (hf : StrictMonoOn f (Ioo (-δ) δ)) (hf0 : f 0 = 0)
    (hx : x ∈ Ioo (-δ) δ) :
    (0 < f x ↔ 0 < x) ∧ (f x = 0 ↔ x = 0) ∧ (0 ≤ f x ↔ 0 ≤ x) := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  exact ⟨by simpa [hf0] using hf.lt_iff_lt h0 hx,
    by simpa [hf0] using hf.eq_iff_eq hx h0,
    by simpa [hf0] using hf.le_iff_le h0 hx⟩



theorem exists_first_coordinate_sign_radius {f : ℝ × ℝ → ℝ}
    (hf : ContDiffAt ℝ 1 f 0)
    (hpositive : 0 < fderiv ℝ f 0 (1, 0))
    (hzero : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → f q = 0) :
    ∃ δ > 0, ∀ r t : ℝ, |r| < δ → |t| < δ →
      (0 < f (r, t) ↔ 0 < r) ∧ (f (r, t) = 0 ↔ r = 0) ∧
        (0 ≤ f (r, t) ↔ 0 ≤ r) := by
  let d (q : ℝ × ℝ) := fderiv ℝ f q (1, 0)
  have hd : ContinuousAt d 0 :=
    (hf.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hpos : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), 0 < d q :=
    hd.eventually (eventually_gt_nhds hpositive)
  have hgood : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ),
      DifferentiableAt ℝ f q ∧ 0 < d q ∧ (q.1 = 0 → f q = 0) := by
    filter_upwards [hf.eventually (by simp), hpos, hzero] with q hq hp hz
    exact ⟨hq.differentiableAt_one, hp, hz⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hlocal {r t : ℝ} (hr : |r| < δ) (ht : |t| < δ) :=
    hball (show (r, t) ∈ ball (0 : ℝ × ℝ) δ by
      simpa only [mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        max_lt_iff] using And.intro hr ht)
  refine ⟨δ, hδ, ?_⟩
  intro r t hr ht
  have hderiv : ∀ u ∈ Ioo (-δ) δ,
      HasDerivAt (fun u => f (u, t)) (d (u, t)) u := by
    intro u hu
    exact (hlocal (abs_lt.mpr hu) ht).1.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u t))
  have hmono : StrictMonoOn (fun u => f (u, t)) (Ioo (-δ) δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (-δ) δ)
    · exact fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Ioo (-δ) δ := interior_subset hu
      rw [(hderiv u hu').deriv]
      exact (hlocal (abs_lt.mpr hu') ht).2.1
  exact signs_of_strictMonoOn hδ hmono
    ((hlocal (r := 0) (by simpa using hδ) ht).2.2 rfl) (abs_lt.mp hr)




theorem exists_quadrant_preserving_radius {K : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    (hK : ContDiffAt ℝ 1 K (0, (0, 0)))
    (hdK : HasFDerivAt K (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) (0, (0, 0)))
    (haxes : ∀ᶠ p in 𝓝 (0, (0, 0)),
      (p.2.1 = 0 → (K p).1 = 0) ∧ (p.2.2 = 0 → (K p).2 = 0)) :
    ∃ δ > 0, ∀ ε s t : ℝ, |ε| < δ → |s| < δ → |t| < δ →
      ((0 < (K (ε, (s, t))).1 ↔ 0 < s) ∧
        ((K (ε, (s, t))).1 = 0 ↔ s = 0) ∧
        (0 ≤ (K (ε, (s, t))).1 ↔ 0 ≤ s)) ∧
      ((0 < (K (ε, (s, t))).2 ↔ 0 < t) ∧
        ((K (ε, (s, t))).2 = 0 ↔ t = 0) ∧
        (0 ≤ (K (ε, (s, t))).2 ↔ 0 ≤ t)) := by
  let d₁ (p : ℝ × (ℝ × ℝ)) : ℝ := (fderiv ℝ K p (0, (1, 0))).1
  let d₂ (p : ℝ × (ℝ × ℝ)) : ℝ := (fderiv ℝ K p (0, (0, 1))).2
  have hc₁ : ContinuousAt d₁ (0, (0, 0)) :=
    ((hK.continuousAt_fderiv (by simp)).clm_apply continuousAt_const).fst
  have hc₂ : ContinuousAt d₂ (0, (0, 0)) :=
    ((hK.continuousAt_fderiv (by simp)).clm_apply continuousAt_const).snd
  have hp₁ : ∀ᶠ p in 𝓝 (0, (0, 0)), 0 < d₁ p :=
    hc₁.eventually (eventually_gt_nhds (by simp [d₁, hdK.fderiv]))
  have hp₂ : ∀ᶠ p in 𝓝 (0, (0, 0)), 0 < d₂ p :=
    hc₂.eventually (eventually_gt_nhds (by simp [d₂, hdK.fderiv]))
  have hgood : ∀ᶠ p in 𝓝 (0, (0, 0)),
      DifferentiableAt ℝ K p ∧ 0 < d₁ p ∧ 0 < d₂ p ∧
        (p.2.1 = 0 → (K p).1 = 0) ∧ (p.2.2 = 0 → (K p).2 = 0) := by
    filter_upwards [hK.eventually (by simp), hp₁, hp₂, haxes] with p hp h₁ h₂ ha
    exact ⟨hp.differentiableAt_one, h₁, h₂, ha⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hlocal {ε s t : ℝ} (hε : |ε| < δ) (hs : |s| < δ) (ht : |t| < δ) :=
    hball (show (ε, (s, t)) ∈ ball (0, (0, 0)) δ by
      change dist (ε, (s, t)) 0 < δ
      simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        max_lt_iff] using And.intro hε (And.intro hs ht))
  refine ⟨δ, hδ, ?_⟩
  intro ε s t hε hs ht
  have hzero : |(0 : ℝ)| < δ := by simpa using hδ
  have hd₁ : ∀ u ∈ Ioo (-δ) δ,
      HasDerivAt (fun u => (K (ε, (u, t))).1) (d₁ (ε, (u, t))) u := by
    intro u hu
    have hpath : HasDerivAt (fun u : ℝ => (ε, (u, t))) (0, (1, 0)) u :=
      (hasDerivAt_const u ε).prodMk ((hasDerivAt_id u).prodMk (hasDerivAt_const u t))
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', d₁] using
      (hlocal hε (abs_lt.mpr hu) ht).1.hasFDerivAt.fst.comp_hasDerivAt u hpath
  have hm₁ : StrictMonoOn (fun u => (K (ε, (u, t))).1) (Ioo (-δ) δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (-δ) δ)
    · exact fun u hu => (hd₁ u hu).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Ioo (-δ) δ := interior_subset hu
      rw [(hd₁ u hu').deriv]
      exact (hlocal hε (abs_lt.mpr hu') ht).2.1
  have hz₁ : (K (ε, (0, t))).1 = 0 := (hlocal hε hzero ht).2.2.2.1 rfl
  have hd₂ : ∀ u ∈ Ioo (-δ) δ,
      HasDerivAt (fun u => (K (ε, (s, u))).2) (d₂ (ε, (s, u))) u := by
    intro u hu
    have hpath : HasDerivAt (fun u : ℝ => (ε, (s, u))) (0, (0, 1)) u :=
      (hasDerivAt_const u ε).prodMk ((hasDerivAt_const u s).prodMk (hasDerivAt_id u))
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', d₂] using
      (hlocal hε hs (abs_lt.mpr hu)).1.hasFDerivAt.snd.comp_hasDerivAt u hpath
  have hm₂ : StrictMonoOn (fun u => (K (ε, (s, u))).2) (Ioo (-δ) δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (-δ) δ)
    · exact fun u hu => (hd₂ u hu).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Ioo (-δ) δ := interior_subset hu
      rw [(hd₂ u hu').deriv]
      exact (hlocal hε hs (abs_lt.mpr hu')).2.2.1
  have hz₂ : (K (ε, (s, 0))).2 = 0 := (hlocal hε hs hzero).2.2.2.2 rfl
  exact ⟨signs_of_strictMonoOn hδ hm₁ hz₁ (abs_lt.mp hs),
    signs_of_strictMonoOn hδ hm₂ hz₂ (abs_lt.mp ht)⟩

end Poincare.Analysis
