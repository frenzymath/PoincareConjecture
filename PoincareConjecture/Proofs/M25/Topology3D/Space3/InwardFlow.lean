import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowAlgebra
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue











set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem inwardField_radial_bound (f : E → E) {K : ℝ≥0} (hK : LipschitzWith K f)
    (hin : ∀ q : E, ‖q‖ = 1 → ⟪q, f q⟫_ℝ ≤ 0)
    (x : E) (hx : 1 ≤ ‖x‖) :
    2 * ⟪x, f x⟫_ℝ ≤ 2 * (K : ℝ) * (‖x‖ ^ 2 - 1) := by
  let r : ℝ := ‖x‖
  let q : E := r⁻¹ • x
  have hr : 0 < r := zero_lt_one.trans_le hx
  have hq : ‖q‖ = 1 := by
    rw [show q = r⁻¹ • x from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hxq : r • q = x := by
    dsimp [q]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hdist : ‖x - q‖ = r - 1 := by
    calc
      ‖x - q‖ = ‖(r - 1) • q‖ := by rw [sub_smul, one_smul, hxq]
      _ = r - 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx), hq, mul_one]
  have hi : ⟪q, f x⟫_ℝ ≤ (K : ℝ) * (r - 1) := by
    calc
      ⟪q, f x⟫_ℝ = ⟪q, f x - f q⟫_ℝ + ⟪q, f q⟫_ℝ := by
        rw [inner_sub_right]
        ring
      _ ≤ ‖f x - f q‖ := by
        have hcs := real_inner_le_norm q (f x - f q)
        rw [hq, one_mul] at hcs
        linarith [hin q hq]
      _ ≤ (K : ℝ) * (r - 1) := by
        simpa only [hdist] using hK.norm_sub_le x q
  have hinner : ⟪x, f x⟫_ℝ = r * ⟪q, f x⟫_ℝ := by
    rw [← hxq, real_inner_smul_left]
  change 2 * ⟪x, f x⟫_ℝ ≤ 2 * (K : ℝ) * (r ^ 2 - 1)
  rw [hinner]
  calc
    2 * (r * ⟪q, f x⟫_ℝ) ≤ 2 * (r * ((K : ℝ) * (r - 1))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi hr.le) (by norm_num)
    _ ≤ 2 * (K : ℝ) * (r ^ 2 - 1) := by
      nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr hx)]



theorem boundedFlow_mapsTo_closedBall [CompleteSpace E]
    (f : E → E) {K L : ℝ≥0} (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (hin : ∀ q : E, ‖q‖ = 1 → ⟪q, f q⟫_ℝ ≤ 0)
    (t : ℝ) (ht : 0 ≤ t) :
    MapsTo (fun x => boundedFlow f hK hL x t) (closedBall 0 1) (closedBall 0 1) := by
  intro x hx
  let c := boundedFlow f hK hL x
  let C : ℝ := 2 * K + 1
  have hd (u : ℝ) : HasDerivAt (fun v => ‖c v‖ ^ 2) (2 * ⟪c u, f (c u)⟫_ℝ) u :=
    (boundedFlow_hasDerivAt f hK hL x u).norm_sq
  have hf : ContinuousOn (fun u => ‖c u‖ ^ 2) (Icc 0 t) :=
    fun u _ => (hd u).continuousAt.continuousWithinAt
  have hbarrier (eps : ℝ) (heps : 0 < eps) :
      ‖c t‖ ^ 2 ≤ 1 + eps * Real.exp (C * t) := by
    have hb (u : ℝ) : HasDerivAt (fun v => 1 + eps * Real.exp (C * v))
        (C * (eps * Real.exp (C * u))) u := by
      simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using
        ((((hasDerivAt_id u).const_mul C).exp).const_mul eps).const_add 1
    apply image_le_of_deriv_right_lt_deriv_boundary hf
      (fun u _ => (hd u).hasDerivWithinAt) (B := fun u => 1 + eps * Real.exp (C * u))
      ?_ hb ?_ ⟨ht, le_rfl⟩
    · have hx' := mem_closedBall_zero_iff.mp hx
      simp only [c, boundedFlow_zero, mul_zero, Real.exp_zero, mul_one]
      nlinarith [norm_nonneg x]
    · intro u _ hu
      have hp : 0 < eps * Real.exp (C * u) := mul_pos heps (Real.exp_pos _)
      have hu1 : 1 ≤ ‖c u‖ := by nlinarith [norm_nonneg (c u)]
      have hv := inwardField_radial_bound f hK hin (c u) hu1
      rw [hu, add_sub_cancel_left] at hv
      dsimp [C] at *
      nlinarith
  have hnormsq : ‖c t‖ ^ 2 ≤ 1 := by
    apply le_of_forall_pos_le_add
    intro eps heps
    have h := hbarrier (eps / Real.exp (C * t)) (div_pos heps (Real.exp_pos _))
    simpa only [div_mul_cancel₀ _ (Real.exp_ne_zero _)] using h
  apply mem_closedBall_zero_iff.mpr
  change ‖c t‖ ≤ 1
  nlinarith [norm_nonneg (c t)]

end PoincareConjecture.M25.Topology3D
