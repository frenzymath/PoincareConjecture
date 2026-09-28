import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorTemplates

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private theorem raised_return_active_angle (h t : ℝ) (hsmall : h < 1 / 1024)
    (ht : t ∈ Ioo h (1 - h)) :
    3 * Real.pi / 4 < raisedReturnAngle h t ∧
      raisedReturnAngle h t < 9 * Real.pi / 4 := by
  have hd : 0 < 1 - 2 * h := by linarith
  have ha0 : 0 < (t - h) / (1 - 2 * h) :=
    div_pos (sub_pos.mpr ht.1) hd
  have ha1 : (t - h) / (1 - 2 * h) < 1 :=
    (div_lt_one hd).mpr (by linarith [ht.2])
  have hq0 : 0 < raisedReturnQ h t :=
    Real.smoothTransition.pos_of_pos ha0
  have hq1 : raisedReturnQ h t < 1 :=
    Real.smoothTransition.lt_one_of_lt_one ha1
  unfold raisedReturnAngle
  constructor <;> nlinarith [Real.pi_pos]

private theorem raised_return_outer_port_polar
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (outer e : Fin 2) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let theta : ℝ := if e = 0 then 9 * Real.pi / 4 else 3 * Real.pi / 4
    J2.symm (sx (ep (outer, e)) / Real.sqrt 2,
      sy (ep (outer, e)) / Real.sqrt 2) =
      J2.symm (raisedReturnSign outer * Real.cos theta,
        raisedReturnSign outer * Real.sin theta) := by
  have hsqrt : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    apply (eq_div_iff (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))).2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hc0 : Real.cos (9 * Real.pi / 4) = 1 / Real.sqrt 2 := by
    rw [show 9 * Real.pi / 4 = Real.pi / 4 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi_div_four, hsqrt]
  have hs0 : Real.sin (9 * Real.pi / 4) = 1 / Real.sqrt 2 := by
    rw [show 9 * Real.pi / 4 = Real.pi / 4 + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_pi_div_four, hsqrt]
  have hc1 : Real.cos (3 * Real.pi / 4) = -(1 / Real.sqrt 2) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four, hsqrt]
  have hs1 : Real.sin (3 * Real.pi / 4) = 1 / Real.sqrt 2 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_four, hsqrt]
  fin_cases outer <;> fin_cases e <;>
    simp [finProdFinEquiv, raisedReturnSign, hc0, hs0, hc1, hs1] <;> ring

theorem saddle_nested_raised_return_active_geometry
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) (inner : Fin 2) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let outer : Fin 2 := raisedReturnOther inner
    let Ray : Set E2 :=
      ((fun r : ℝ => r • port (ep (outer, 0))) '' Icc 1 (1 + 32 * h)) ∪
      ((fun r : ℝ => r • port (ep (outer, 1))) '' Icc 1 (1 + 32 * h))
    let gamma : ℝ → E2 := raisedReturnPhysicalCurve kappa J2 h inner
    (gamma '' Ioo h (1 - h) ⊆
      kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) ∧
      Disjoint (gamma '' Ioo h (1 - h)) (kappa '' Ray) ∧
      Disjoint (gamma '' Ioo h (1 - h))
        (kappa '' closedBall (0 : E2) 1) ∧
      IsPreconnected (gamma '' Ioo h (1 - h)) := by
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let port : Fin 4 → E2 := fun a =>
    J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let outer : Fin 2 := raisedReturnOther inner
  let Ray : Set E2 :=
    ((fun r : ℝ => r • port (ep (outer, 0))) '' Icc 1 (1 + 32 * h)) ∪
    ((fun r : ℝ => r • port (ep (outer, 1))) '' Icc 1 (1 + 32 * h))
  let g : ℝ → E2 := raisedReturnPlanarCurve J2 h inner
  let gamma : ℝ → E2 := raisedReturnPhysicalCurve kappa J2 h inner
  change (gamma '' Ioo h (1 - h) ⊆
      kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) ∧
    Disjoint (gamma '' Ioo h (1 - h)) (kappa '' Ray) ∧
    Disjoint (gamma '' Ioo h (1 - h)) (kappa '' closedBall (0 : E2) 1) ∧
    IsPreconnected (gamma '' Ioo h (1 - h))
  have hsrc {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ kappa.source :=
    hkappaSource (by simpa only [mem_closedBall_zero_iff] using hx)
  have hportNorm (a : Fin 4) : ‖port a‖ = 1 := by
    have hn := hJ2 (port a)
    have hs : (sx a) ^ 2 = 1 ∧ (sy a) ^ 2 = 1 := by
      fin_cases a <;> norm_num [sx, sy]
    simp only [port, J2.apply_symm_apply] at hn
    rw [div_pow, div_pow, hs.1, hs.2,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
    norm_num at hn
    nlinarith [norm_nonneg (port a)]
  have hnorm (t : ℝ) : ‖g t‖ = raisedReturnRadius h t :=
    raisedReturnPlanar_norm_eq_radius J2 hJ2 h inner t
      (raisedReturnRadius_nonneg h hh t)
  have hradial (t : ℝ) (ht : t ∈ Ioo h (1 - h)) :
      1 < ‖g t‖ ∧ ‖g t‖ ≤ 1 + 32 * h ∧ ‖g t‖ < 2 := by
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [hnorm t]
    have hlo := raisedReturnRadius_lower h hh t
    have hhi := raisedReturnRadius_upper_closed h hh hsmall t ht01
    constructor
    · linarith
    · constructor <;> linarith
  have hsource (t : ℝ) (ht : t ∈ Ioo h (1 - h)) : g t ∈ kappa.source :=
    hsrc (hradial t ht).2.2.le
  have hplanarAvoid (t : ℝ) (ht : t ∈ Ioo h (1 - h))
      (e : Fin 2) (r : ℝ) (hr : 0 < r) : g t ≠ r • port (ep (outer, e)) := by
    intro heq
    let s : ℝ := raisedReturnSign outer
    let theta : ℝ := if e = 0 then 9 * Real.pi / 4 else 3 * Real.pi / 4
    have hs : s ≠ 0 := by
      have hs2 : s ^ 2 = 1 := raisedReturnSign_sq outer
      intro hz
      rw [hz] at hs2
      norm_num at hs2
    have hp : port (ep (outer, e)) =
        J2.symm (s * Real.cos theta, s * Real.sin theta) :=
      raised_return_outer_port_polar J2 outer e
    have heJ := congrArg J2 heq
    rw [hp] at heJ
    simp only [g, raisedReturnPlanarCurve, map_smul, J2.apply_symm_apply] at heJ
    have hx := congrArg Prod.fst heJ
    have hy := congrArg Prod.snd heJ
    change s * raisedReturnRadius h t * Real.cos (raisedReturnAngle h t) =
      r * (s * Real.cos theta) at hx
    change s * raisedReturnRadius h t * Real.sin (raisedReturnAngle h t) =
      r * (s * Real.sin theta) at hy
    have hePolar :
        (raisedReturnRadius h t * Real.cos (raisedReturnAngle h t),
          raisedReturnRadius h t * Real.sin (raisedReturnAngle h t)) =
        (r * Real.cos theta, r * Real.sin theta) := by
      apply Prod.ext
      · apply mul_left_cancel₀ hs
        nlinarith only [hx]
      · apply mul_left_cancel₀ hs
        nlinarith only [hy]
    have htAngle := raised_return_active_angle h t hsmall ht
    have htheta : theta ∈ Icc (3 * Real.pi / 4) (9 * Real.pi / 4) := by
      dsimp only [theta]
      split_ifs <;> constructor <;> linarith [Real.pi_pos]
    have hR : 0 < raisedReturnRadius h t := by
      rw [← hnorm t]
      linarith [(hradial t ht).1]
    have hangle := (Real.polar_parameters_eq_of_mem_Icc hR hr
      ⟨htAngle.1.le, htAngle.2.le⟩ htheta (by linarith [Real.pi_pos]) hePolar).2
    fin_cases e <;> simp [theta] at hangle <;> linarith [htAngle.1, htAngle.2]
  have hAnnular : gamma '' Ioo h (1 - h) ⊆
      kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h} := by
    rintro y ⟨t, ht, rfl⟩
    exact ⟨g t, ⟨(hradial t ht).1.le, (hradial t ht).2.1⟩, rfl⟩
  have hRays : Disjoint (gamma '' Ioo h (1 - h)) (kappa '' Ray) := by
    apply disjoint_left.mpr
    rintro y ⟨t, ht, rfl⟩ ⟨x, hx, heq⟩
    have hrepr : ∃ e : Fin 2, ∃ r ∈ Icc (1 : ℝ) (1 + 32 * h),
        x = r • port (ep (outer, e)) := by
      rcases hx with hx | hx
      · obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨0, r, hr, rfl⟩
      · obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨1, r, hr, rfl⟩
    obtain ⟨e, r, hr, rfl⟩ := hrepr
    have hr0 : 0 < r := by linarith [hr.1]
    have hn : ‖r • port (ep (outer, e))‖ = r := by
      rw [norm_smul, hportNorm, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
    have hrSource : r • port (ep (outer, e)) ∈ kappa.source := by
      apply hsrc
      rw [hn]
      linarith [hr.2]
    have hxy : g t = r • port (ep (outer, e)) :=
      kappa.injOn (hsource t ht) hrSource heq.symm
    exact hplanarAvoid t ht e r hr0 hxy
  have hUnit : Disjoint (gamma '' Ioo h (1 - h))
      (kappa '' closedBall (0 : E2) 1) := by
    apply disjoint_left.mpr
    rintro y ⟨t, ht, rfl⟩ ⟨x, hx, heq⟩
    have hxn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall_zero_iff] using hx
    have hxs : x ∈ kappa.source := hsrc (by linarith)
    have hxy : g t = x := kappa.injOn (hsource t ht) hxs heq.symm
    have hn := (hradial t ht).1
    rw [hxy] at hn
    linarith
  have hcontinuous : ContinuousOn gamma (Ioo h (1 - h)) :=
    kappa.continuousOn.comp
      (raisedReturnPlanar_contDiff J2 h inner).continuous.continuousOn hsource
  exact ⟨hAnnular, hRays, hUnit, isPreconnected_Ioo.image gamma hcontinuous⟩

end PoincareConjecture.M25.Topology3D
