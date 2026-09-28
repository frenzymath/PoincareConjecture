import PoincareConjecture.Proofs.M25.Topology3D.Space3.CapContraction
import PoincareConjecture.Proofs.M25.Topology3D.Space3.InwardFlow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set Metric
open scoped ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (χ : ℝ → ℝ) (hχ : ∀ z, χ z ∈ Icc 0 1)
variable (hzero : ∀ z, z ≤ 1 / 2 → χ z = 0) (u : E) (hu : ‖u‖ = 1)
variable (f : E → E) {K L : ℝ≥0} (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
variable (hag : EqOn f (capContractionField χ u) (closedBall 0 1))

include hχ hzero hu hag

theorem capFlow_mapsTo_closedBall (t : ℝ) (ht : 0 ≤ t) :
    MapsTo (fun x => boundedFlow f hK hL x t) (closedBall 0 1) (closedBall 0 1) := by
  apply boundedFlow_mapsTo_closedBall f hK hL ?_ t ht
  intro x hx
  rw [hag (mem_closedBall_zero_iff.mpr hx.le)]
  exact capContractionField_inward χ hχ hzero u hu x hx

theorem capFlow_distance_sq_le (x : E) (hx : x ∈ closedBall 0 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖boundedFlow f hK hL x t - u‖ ^ 2 ≤ Real.exp (-t) * ‖x - u‖ ^ 2 := by
  let c := boundedFlow f hK hL x
  have hmem (s : ℝ) (hs : 0 ≤ s) : c s ∈ closedBall 0 1 :=
    capFlow_mapsTo_closedBall χ hχ hzero u hu f hK hL hag s hs hx
  have hd (s : ℝ) : HasDerivAt (fun v => Real.exp v * ‖c v - u‖ ^ 2)
      (Real.exp s * ‖c s - u‖ ^ 2 +
        Real.exp s * (2 * ⟪c s - u, f (c s)⟫_ℝ)) s := by
    exact (Real.hasDerivAt_exp s).mul
      ((boundedFlow_hasDerivAt f hK hL x s).sub_const u).norm_sq
  have hmono : AntitoneOn (fun s => Real.exp s * ‖c s - u‖ ^ 2) (Icc 0 t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs
    have hm := hmem s (interior_subset hs).1
    have hdec := capContractionField_attraction χ hχ hzero u hu (c s)
      (mem_closedBall_zero_iff.mp hm)
    rw [hag hm]
    have hp := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos s).le
      (show ‖c s - u‖ ^ 2 + 2 * ⟪c s - u, capContractionField χ u (c s)⟫_ℝ ≤ 0 by
        linarith)
    nlinarith only [hp]
  have hbound := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only [c, boundedFlow_zero, Real.exp_zero, one_mul] at hbound
  calc
    ‖boundedFlow f hK hL x t - u‖ ^ 2 =
        Real.exp (-t) * (Real.exp t * ‖boundedFlow f hK hL x t - u‖ ^ 2) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-t) * ‖x - u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le

theorem capFlow_height_mono (x : E) (hx : x ∈ closedBall 0 1) :
    MonotoneOn (fun t => ⟪u, boundedFlow f hK hL x t⟫_ℝ) (Ici 0) := by
  let c := boundedFlow f hK hL x
  have hd (s : ℝ) : HasDerivAt (fun v => ⟪u, c v⟫_ℝ) ⟪u, f (c s)⟫_ℝ s :=
    (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt s (boundedFlow_hasDerivAt f hK hL x s)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun s _ => (hd s).continuousAt.continuousWithinAt)
    (fun s _ => (hd s).hasDerivWithinAt)
  intro s hs
  have hm := capFlow_mapsTo_closedBall χ hχ hzero u hu f hK hL hag s
    (interior_subset hs) hx
  have hz : ⟪u, c s⟫_ℝ ≤ 1 := by
    have h := real_inner_le_norm u (c s)
    rw [hu, one_mul] at h
    exact h.trans (mem_closedBall_zero_iff.mp hm)
  obtain ⟨hlow, hupp, _⟩ := capContractionCoefficient_bounds χ hχ hzero _ hz
  rw [hag hm, capContractionField, inner_sub_right, real_inner_self_eq_norm_sq,
    hu, one_pow, real_inner_smul_right]
  by_cases hz0 : 0 ≤ ⟪u, c s⟫_ℝ
  · nlinarith [mul_le_mul_of_nonneg_right hupp hz0]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith :
        0 ≤ capContractionCoefficient χ ⟪u, c s⟫_ℝ) (le_of_not_ge hz0)]

end PoincareConjecture.M25.Topology3D
