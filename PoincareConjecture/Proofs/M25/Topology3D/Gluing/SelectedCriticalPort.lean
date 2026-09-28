import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped Matrix

namespace PoincareConjecture.M25.Topology3D

theorem saddle_selected_critical_port
    (rho delta : ℝ) (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta ≤ rho ^ 2 / 128)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
    (kp : OpenPartialHomeomorph E2 E2)
    (hksSource : closedBall (0 : E2) 2 ⊆ ks.source)
    (E : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere)
    (hESource : ∀ k : Fin 4, (E k).source =
      Ioo (-2 * delta) (2 * delta) ×ˢ Ioo (-(1 / 8) : ℝ) (1 / 8))
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (C1 : Fin 2 → UnitCircle → E2)
    (oldLevel : Set UnitTwoSphere)
    (hLevel : (⋃ i : Fin 2, range (q i)) = oldLevel)
    (F1 : E2 → E2) (exterior : UnitTwoSphere → E2)
    (P kappa : E2 → E2)
    (hPlacement : EqOn (fun x => P (kp x)) kappa (closedBall (0 : E2) 2)) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let X : ℝ → ℝ → Fin 4 → E2 := fun z r k => J2.symm
      (sx k * Real.sqrt ((r ^ 2 + z) / 2),
        sy k * Real.sqrt ((r ^ 2 - z) / 2))
    let port : Fin 4 → E2 := fun k =>
      J2.symm (sx k / Real.sqrt 2, sy k / Real.sqrt 2)
    (∀ (k : Fin 4) (w : ℝ × ℝ), w ∈ (E k).source →
      E k w = ks (X (w.1 / rho ^ 2) (1 + w.2) k)) →
    (∀ (i : Fin 2) (theta : UnitCircle),
      q i theta ∈ ks '' closedBall (0 : E2) 1 →
      C1 i theta = kp (F1 (ks.symm (q i theta)))) →
    (∀ (i : Fin 2) (theta : UnitCircle),
      q i theta ∉ ks '' ball (0 : E2) 1 →
      C1 i theta = exterior (q i theta)) →
    (∀ p ∈ oldLevel, p ∈ ks.target →
      7 / 8 < ‖ks.symm p‖ → ‖ks.symm p‖ < 9 / 8 →
      kp (F1 (ks.symm p)) = exterior p) →
    (∀ (k : Fin 4) (a : ℝ), a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) →
      F1 (X (-delta / rho ^ 2) (1 + a) k) = X 0 (1 + a) k) →
    ∀ (k : Fin 4) (a : ℝ), a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) →
      ∀ (i : Fin 2) (theta : UnitCircle), q i theta = E k (-delta, a) →
        C1 i theta = kp ((1 + a) • port k) ∧
        P (C1 i theta) = kappa ((1 + a) • port k) := by
  intro sx sy X port hPortNative hInside hOutside hOverlap hAngularOne
    k a ha i theta hp
  let mu : ℝ := delta / rho ^ 2
  let x : E2 := X (-delta / rho ^ 2) (1 + a) k
  have hmu : 0 < mu := div_pos hdelta (sq_pos_of_pos hrho)
  have hmuSmall : mu ≤ 1 / 128 := by
    apply (div_le_iff₀ (sq_pos_of_pos hrho)).2
    nlinarith only [hsmall]
  have hnegative : -delta / rho ^ 2 = -mu := by dsimp only [mu]; ring
  have hsign : (sx k) ^ 2 = 1 ∧ (sy k) ^ 2 = 1 := by
    fin_cases k <;> norm_num [sx, sy]
  have hplus : 0 ≤ ((1 + a) ^ 2 - mu) / 2 := by
    nlinarith only [ha.1, hmuSmall, sq_nonneg (1 + a - 7 / 8)]
  have hminus : 0 ≤ ((1 + a) ^ 2 + mu) / 2 :=
    div_nonneg (add_nonneg (sq_nonneg _) hmu.le) (by norm_num)
  have hnorm : ‖x‖ = 1 + a := by
    have hsquare : ‖x‖ ^ 2 = (1 + a) ^ 2 := by
      rw [← hJ2 x]
      simp only [x, X, ContinuousLinearEquiv.apply_symm_apply,
        hnegative, ← sub_eq_add_neg, sub_neg_eq_add, mul_pow,
        hsign.1, hsign.2, one_mul, Real.sq_sqrt hplus, Real.sq_sqrt hminus]
      ring
    nlinarith only [hsquare, norm_nonneg x, ha.1]
  have hx : x ∈ closedBall (0 : E2) 2 :=
    mem_closedBall_zero_iff.mpr (by rw [hnorm]; linarith only [ha.2])
  have hxs : x ∈ ks.source := hksSource hx
  have hEndpoint : (-delta, a) ∈ (E k).source := by
    rw [hESource k]
    exact ⟨⟨by linarith only [hdelta], by linarith only [hdelta]⟩, ha⟩
  have hpoint : q i theta = ks x := hp.trans (hPortNative k (-delta, a) hEndpoint)
  have hinverse : ks.symm (q i theta) = x := by rw [hpoint, ks.left_inv hxs]
  have htarget : q i theta ∈ ks.target := by
    rw [hpoint]
    exact ks.map_source hxs
  have hlevel : q i theta ∈ oldLevel := by
    rw [← hLevel]
    exact mem_iUnion.mpr ⟨i, mem_range_self theta⟩
  have hsame : C1 i theta = kp (F1 x) := by
    by_cases hinside : q i theta ∈ ks '' ball (0 : E2) 1
    · rw [hInside i theta ((image_mono ball_subset_closedBall) hinside), hinverse]
    · rw [hOutside i theta hinside]
      have hover := hOverlap (q i theta) hlevel htarget
        (by rw [hinverse, hnorm]; linarith only [ha.1])
        (by rw [hinverse, hnorm]; linarith only [ha.2])
      simpa only [hinverse] using hover.symm
  have hRadius : 0 < 1 + a := by linarith only [ha.1]
  have hzero : X 0 (1 + a) k = (1 + a) • port k := by
    have hs : Real.sqrt ((1 + a) ^ 2 / 2) = (1 + a) / Real.sqrt 2 := by
      rw [Real.sqrt_div (sq_nonneg (1 + a)), Real.sqrt_sq_eq_abs, abs_of_pos hRadius]
    apply J2.injective
    simp only [X, port, add_zero, sub_zero, hs, map_smul, J2.apply_symm_apply,
      Prod.smul_mk, smul_eq_mul]
    congr 1 <;> ring
  have hnative : C1 i theta = kp ((1 + a) • port k) := by
    rw [hsame, hAngularOne k a ha, hzero]
  have hPortNorm : ‖port k‖ = 1 := by
    have hsquare : ‖port k‖ ^ 2 = 1 := by
      rw [← hJ2 (port k)]
      simp only [port, J2.apply_symm_apply, div_pow, hsign.1, hsign.2,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    nlinarith only [hsquare, norm_nonneg (port k)]
  have hradial : (1 + a) • port k ∈ closedBall (0 : E2) 2 := by
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRadius, hPortNorm, mul_one]
    linarith only [ha.2]
  refine ⟨hnative, ?_⟩
  rw [hnative]
  exact hPlacement hradial

end PoincareConjecture.M25.Topology3D
