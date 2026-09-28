import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorTemplates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem saddle_nested_raised_long_return_midpoint_inside
    (kappa : OpenPartialHomeomorph E2 E2)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) (inner : Fin 2)
    (Bi Bo : BallNeighborhoodChart E2 E2)
    (hAnnularInside : kappa '' {x : E2 |
      1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
        |(J2 x).1| < raisedReturnSign inner * (J2 x).2} ⊆ Bi.inside)
    (hNested : Bi.closedRegion ⊆ Bo.inside) :
    raisedReturnPhysicalCurve kappa J2 h inner (1 / 2) ∈ Bo.inside := by
  let x : E2 := J2.symm (0, raisedReturnSign inner * (1 + 10 * h))
  have hx : ‖x‖ = 1 + 10 * h := by
    have hn := hJ2 x
    simp only [x, J2.apply_symm_apply, mul_pow, raisedReturnSign_sq,
      one_mul, zero_pow (by norm_num : 2 ≠ 0), zero_add] at hn
    nlinarith [norm_nonneg x]
  have hcone : |(J2 x).1| < raisedReturnSign inner * (J2 x).2 := by
    simp only [x, J2.apply_symm_apply, abs_zero]
    rw [← mul_assoc, ← pow_two, raisedReturnSign_sq, one_mul]
    linarith
  have hi : kappa x ∈ Bi.inside :=
    hAnnularInside ⟨x, ⟨by rw [hx]; linarith,
      by rw [hx]; linarith, hcone⟩, rfl⟩
  rw [raisedReturnPhysicalCurve, raisedReturn_mid_formula h hh hsmall]
  apply hNested
  rw [← Bi.inside_union_boundary]
  exact Or.inl hi

set_option maxHeartbeats 600000 in

theorem raisedReturn_physical_end_formulas
    (kappa : OpenPartialHomeomorph E2 E2)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) (inner : Fin 2) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    ∀ t : ℝ,
      (t ≤ h → raisedReturnPhysicalCurve kappa J2 h inner t =
        kappa ((1 + 3 * h - t) • port (ep (raisedReturnOther inner, 1)))) ∧
      (1 - h ≤ t → raisedReturnPhysicalCurve kappa J2 h inner t =
        kappa ((1 + 3 * h + t - 1) • port (ep (raisedReturnOther inner, 0)))) := by
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun a =>
    J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  change ∀ t : ℝ,
    (t ≤ h → raisedReturnPhysicalCurve kappa J2 h inner t =
      kappa ((1 + 3 * h - t) • port (ep (raisedReturnOther inner, 1)))) ∧
    (1 - h ≤ t → raisedReturnPhysicalCurve kappa J2 h inner t =
      kappa ((1 + 3 * h + t - 1) • port (ep (raisedReturnOther inner, 0))))
  have hsqrt : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    apply (div_eq_div_iff (by norm_num) (Real.sqrt_pos.mpr (by norm_num)).ne').mpr
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hcos3 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
  have hsin3 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_four]
  have hcos9 : Real.cos (9 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [show 9 * Real.pi / 4 = 2 * Real.pi + Real.pi / 4 by ring,
      Real.cos_add, Real.cos_two_pi, Real.sin_two_pi,
      Real.cos_pi_div_four]
    ring
  have hsin9 : Real.sin (9 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [show 9 * Real.pi / 4 = 2 * Real.pi + Real.pi / 4 by ring,
      Real.sin_add, Real.cos_two_pi, Real.sin_two_pi,
      Real.sin_pi_div_four]
    ring
  have hp1 (i : Fin 2) (R : ℝ) :
      J2.symm (raisedReturnSign i * R * Real.cos (3 * Real.pi / 4),
        raisedReturnSign i * R * Real.sin (3 * Real.pi / 4)) =
          R • port (ep (i, 1)) := by
    apply J2.injective
    fin_cases i <;> apply Prod.ext <;>
      norm_num [port, ep, finProdFinEquiv, sx, sy, raisedReturnSign,
        hcos3, hsin3, hsqrt, map_smul] <;> ring
  have hp0 (i : Fin 2) (R : ℝ) :
      J2.symm (raisedReturnSign i * R * Real.cos (9 * Real.pi / 4),
        raisedReturnSign i * R * Real.sin (9 * Real.pi / 4)) =
          R • port (ep (i, 0)) := by
    apply J2.injective
    fin_cases i <;> apply Prod.ext <;>
      norm_num [port, ep, finProdFinEquiv, sx, sy, raisedReturnSign,
        hcos9, hsin9, hsqrt, map_smul] <;> ring
  intro t
  constructor
  · intro ht
    have ha : raisedReturnAngle h t = 3 * Real.pi / 4 := by
      rw [raisedReturnAngle, raisedReturn_q_zero_left h hh hsmall t ht]
      ring
    rw [raisedReturnPhysicalCurve, raisedReturnPlanarCurve,
      raisedReturn_left_formula h hh hsmall t ht, ha, hp1]
  · intro ht
    have ha : raisedReturnAngle h t = 9 * Real.pi / 4 := by
      rw [raisedReturnAngle, raisedReturn_q_one_right h hh hsmall t ht]
      ring
    rw [raisedReturnPhysicalCurve, raisedReturnPlanarCurve,
      raisedReturn_right_formula h hh hsmall t ht, ha, hp0]

theorem saddle_nested_raised_long_return_original_germs
    (kappa : OpenPartialHomeomorph E2 E2)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (h nu : ℝ) (hh : 0 < h) (hhnu : h < nu / 128)
    (hsmall : h < 1 / 1024) (inner : Fin 2) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    ∀ (alpha : ℝ → E2)
      (_hInitial : ∀ t, |t| < nu →
        alpha t = kappa ((1 + t) • port (ep (raisedReturnOther inner, 0))))
      (_hTerminal : ∀ t, |t - 1| < nu →
        alpha t = kappa ((2 - t) • port (ep (raisedReturnOther inner, 1)))),
      (∀ s, |s| < h / 16 →
        raisedReturnPhysicalCurve kappa J2 h inner s = alpha (1 - 3 * h + s)) ∧
      (∀ s, |s - 1| < h / 16 →
        raisedReturnPhysicalCurve kappa J2 h inner s = alpha (3 * h + s - 1)) ∧
      (∀ s ∈ Icc (0 : ℝ) h,
        raisedReturnPhysicalCurve kappa J2 h inner s = alpha (1 - 3 * h + s)) ∧
      (∀ s ∈ Icc (1 - h) 1,
        raisedReturnPhysicalCurve kappa J2 h inner s = alpha (3 * h + s - 1)) := by
  dsimp only
  intro alpha hInitial hTerminal
  have hEnds := raisedReturn_physical_end_formulas kappa J2 h hh hsmall inner
  have hleft (s : ℝ) (hs : -h / 16 < s) (hs' : s ≤ h) :
      raisedReturnPhysicalCurve kappa J2 h inner s = alpha (1 - 3 * h + s) := by
    rw [(hEnds s).1 hs', hTerminal _ (by
      apply abs_lt.mpr
      constructor <;> linarith)]
    congr 2
    ring
  have hright (s : ℝ) (hs : 1 - h ≤ s) (hs' : s < 1 + h / 16) :
      raisedReturnPhysicalCurve kappa J2 h inner s = alpha (3 * h + s - 1) := by
    rw [(hEnds s).2 hs, hInitial _ (by
      apply abs_lt.mpr
      constructor <;> linarith)]
    congr 2
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hleft s (by linarith [(abs_lt.mp hs).1])
      (by linarith [(abs_lt.mp hs).2])
  · intro s hs
    exact hright s (by linarith [(abs_lt.mp hs).1])
      (by linarith [(abs_lt.mp hs).2])
  · intro s hs
    exact hleft s (by linarith [hs.1]) hs.2
  · intro s hs
    exact hright s hs.1 (by linarith [hs.2])

end PoincareConjecture.M25.Topology3D
