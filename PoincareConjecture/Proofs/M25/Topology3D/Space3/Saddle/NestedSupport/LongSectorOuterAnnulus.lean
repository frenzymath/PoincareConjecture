import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorTemplatesScalar

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 600000 in

theorem saddle_nested_outer_arc_avoids_inner_pole
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) (inner : Fin 2) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    ∀ (alpha : ℝ → E2),
      (alpha '' Icc (0 : ℝ) 1) ∩
          (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
        kappa ''
          (((fun r : ℝ => r • port (ep (raisedReturnOther inner, 0))) ''
            Icc 1 (1 + 32 * h)) ∪
          ((fun r : ℝ => r • port (ep (raisedReturnOther inner, 1))) ''
            Icc 1 (1 + 32 * h))) →
      Disjoint
        (kappa '' ((fun r : ℝ => J2.symm (0, raisedReturnSign inner * r)) ''
          Ico 1 (1 + 10 * h)))
        (alpha '' Icc (0 : ℝ) 1) := by
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun a =>
    J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  dsimp only
  intro alpha hAnnular
  change (alpha '' Icc (0 : ℝ) 1) ∩
      (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
    kappa ''
      (((fun r : ℝ => r • port (ep (raisedReturnOther inner, 0))) ''
        Icc 1 (1 + 32 * h)) ∪
      ((fun r : ℝ => r • port (ep (raisedReturnOther inner, 1))) ''
        Icc 1 (1 + 32 * h))) at hAnnular
  have hportN (a : Fin 4) : ‖port a‖ = 1 := by
    have hn := hJ2 (port a)
    have hSigns : (sx a) ^ 2 = 1 ∧ (sy a) ^ 2 = 1 := by
      fin_cases a <;> norm_num [sx, sy]
    simp only [port, J2.apply_symm_apply, div_pow, hSigns.1, hSigns.2,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
    nlinarith [norm_nonneg (port a)]
  have hportCone (i e : Fin 2) (r : ℝ) (hr : 0 ≤ r) :
      |(J2 (r • port (ep (i, e)))).1| =
        raisedReturnSign i * (J2 (r • port (ep (i, e)))).2 := by
    have hsq := Real.sqrt_nonneg (2 : ℝ)
    fin_cases i <;> fin_cases e <;>
      simp [port, ep, finProdFinEquiv, sx, sy, raisedReturnSign, map_smul,
        abs_mul, abs_div, abs_of_nonneg hr, abs_of_nonneg hsq] <;> ring
  apply Set.disjoint_left.mpr
  rintro y ⟨_, ⟨R, hR, rfl⟩, rfl⟩ hyAlpha
  let x : E2 := J2.symm (0, raisedReturnSign inner * R)
  have hxN : ‖x‖ = R := by
    have hn := hJ2 x
    simp only [x, J2.apply_symm_apply, mul_pow, raisedReturnSign_sq,
      one_mul, zero_pow (by norm_num : 2 ≠ 0), zero_add] at hn
    nlinarith [norm_nonneg x, hR.1]
  have hxS : x ∈ kappa.source := by
    apply hkappaSource
    rw [mem_closedBall_zero_iff, hxN]
    linarith [hR.2]
  have hyAnn : kappa x ∈
      kappa '' {z : E2 | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 + 32 * h} := by
    exact ⟨x, ⟨by rw [hxN]; exact hR.1, by rw [hxN]; linarith [hR.2]⟩, rfl⟩
  have hyRay : kappa x ∈
      kappa ''
        (((fun r : ℝ => r • port (ep (raisedReturnOther inner, 0))) ''
          Icc 1 (1 + 32 * h)) ∪
        ((fun r : ℝ => r • port (ep (raisedReturnOther inner, 1))) ''
          Icc 1 (1 + 32 * h))) := by
    rw [← hAnnular]
    exact ⟨hyAlpha, hyAnn⟩
  have hRayFalse (e : Fin 2) (r : ℝ) (hr : r ∈ Icc 1 (1 + 32 * h))
      (he : kappa (r • port (ep (raisedReturnOther inner, e))) = kappa x) : False := by
    have hrN : ‖r • port (ep (raisedReturnOther inner, e))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hr.1]), hportN,
        mul_one]
    have hrS : r • port (ep (raisedReturnOther inner, e)) ∈ kappa.source := by
      apply hkappaSource
      rw [mem_closedBall_zero_iff, hrN]
      linarith [hr.2]
    have heq := kappa.injOn hrS hxS he
    have hcone := hportCone (raisedReturnOther inner) e r (by linarith [hr.1])
    rw [heq] at hcone
    simp only [x, J2.apply_symm_apply, abs_zero, raisedReturnOther_sign] at hcone
    rw [neg_mul, ← mul_assoc, ← pow_two, raisedReturnSign_sq, one_mul] at hcone
    linarith [hR.1]
  rcases hyRay with ⟨z, hz, hzImage⟩
  rcases hz with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · exact hRayFalse 0 r hr hzImage
  · exact hRayFalse 1 r hr hzImage

end PoincareConjecture.M25.Topology3D
