import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryContinuousReflection















set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Metric
open Poincare.Analysis.Sobolev.BoundaryExtension

namespace PoincareConjecture





theorem m64ContinuousBoundaryReflect_holder {u : LoopPlane → ℝ}
    {epsilon R H β : ℝ} (he : epsilon ^ 2 = 1) (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hface : ∀ p ∈ ball (0 : LoopPlane) R, p 0 = 0 → u p = epsilon * u p)
    (hholder : ∀ x ∈ ball (0 : LoopPlane) R, 0 ≤ x 0 →
      ∀ y ∈ ball (0 : LoopPlane) R, 0 ≤ y 0 →
        |u x - u y| ≤ H * ‖x - y‖ ^ β) :
    ∀ x ∈ ball (0 : LoopPlane) R, ∀ y ∈ ball (0 : LoopPlane) R,
      |m64ContinuousBoundaryReflect epsilon u x -
        m64ContinuousBoundaryReflect epsilon u y| ≤ (3 * H) * ‖x - y‖ ^ β := by
  have habs : |epsilon| = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (show epsilon ^ 2 = (1 : ℝ) ^ 2 by simpa using he) with h | h
    · rw [h, abs_one]
    · rw [h, abs_neg, abs_one]
  have hrball (p : LoopPlane) (hp : p ∈ ball (0 : LoopPlane) R) :
      reflect p ∈ ball (0 : LoopPlane) R := by
    simpa only [mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hp
  have hcost (p q : LoopPlane) : H * ‖p - q‖ ^ β ≤ 3 * H * ‖p - q‖ ^ β := by
    nlinarith [mul_nonneg hH (Real.rpow_nonneg (norm_nonneg (p - q)) β)]
  have hmixed (p : LoopPlane) (hp : p ∈ ball (0 : LoopPlane) R) (hp0 : 0 ≤ p 0)
      (q : LoopPlane) (hq : q ∈ ball (0 : LoopPlane) R) (hq0 : q 0 ≤ 0) :
      |u p - epsilon * u (reflect q)| ≤ 3 * H * ‖p - q‖ ^ β := by
    let P : LoopPlane := EuclideanSpace.single 1 (p 1)
    let Q : LoopPlane := EuclideanSpace.single 1 (q 1)
    have hP0 : P 0 = 0 := by simp [P]
    have hQ0 : Q 0 = 0 := by simp [Q]
    have hPball : P ∈ ball (0 : LoopPlane) R := by
      rw [mem_ball_zero_iff]
      have hPn : ‖P‖ ≤ ‖p‖ := by
        simpa only [P, PiLp.norm_single] using PiLp.norm_apply_le p 1
      exact hPn.trans_lt (mem_ball_zero_iff.mp hp)
    have hQball : Q ∈ ball (0 : LoopPlane) R := by
      rw [mem_ball_zero_iff]
      have hQn : ‖Q‖ ≤ ‖q‖ := by
        simpa only [Q, PiLp.norm_single] using PiLp.norm_apply_le q 1
      exact hQn.trans_lt (mem_ball_zero_iff.mp hq)
    have hpP : p - P = EuclideanSpace.single 0 (p 0) := by
      ext i
      fin_cases i <;> simp [P]
    have hqQ : reflect q - Q = EuclideanSpace.single 0 (-q 0) := by
      ext i
      fin_cases i <;> simp [Q]
    have hPQ : P - Q = EuclideanSpace.single 1 (p 1 - q 1) := by
      ext i
      fin_cases i <;> simp [P, Q]
    have hnormal : p 0 - q 0 ≤ ‖p - q‖ := by
      have h := PiLp.norm_apply_le (p - q) 0
      simpa only [PiLp.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr
        (hq0.trans hp0))] using h
    have hpPbound : ‖p - P‖ ≤ ‖p - q‖ := by
      rw [hpP, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg hp0]
      linarith
    have hqQbound : ‖reflect q - Q‖ ≤ ‖p - q‖ := by
      rw [hqQ, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (neg_nonneg.mpr hq0)]
      linarith
    have hPQbound : ‖P - Q‖ ≤ ‖p - q‖ := by
      rw [hPQ, PiLp.norm_single]
      simpa only [PiLp.sub_apply] using PiLp.norm_apply_le (p - q) 1
    have hscale {s t : LoopPlane} (hst : ‖s - t‖ ≤ ‖p - q‖) :
        H * ‖s - t‖ ^ β ≤ H * ‖p - q‖ ^ β :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hst hβ) hH
    have h1 : |u p - u P| ≤ H * ‖p - q‖ ^ β :=
      (hholder p hp hp0 P hPball (by rw [hP0])).trans (hscale hpPbound)
    have h2 : |u P - u Q| ≤ H * ‖p - q‖ ^ β :=
      (hholder P hPball (by rw [hP0]) Q hQball (by rw [hQ0])).trans (hscale hPQbound)
    have h3 : |u Q - epsilon * u (reflect q)| ≤ H * ‖p - q‖ ^ β := by
      calc
        _ = |epsilon * (u Q - u (reflect q))| := by
          rw [mul_sub, ← hface Q hQball hQ0]
        _ = |u Q - u (reflect q)| := by rw [abs_mul, habs, one_mul]
        _ = |u (reflect q) - u Q| := abs_sub_comm _ _
        _ ≤ H * ‖reflect q - Q‖ ^ β := hholder (reflect q) (hrball q hq)
          (by rw [reflect_apply_zero]; exact neg_nonneg.mpr hq0) Q hQball (by rw [hQ0])
        _ ≤ _ := hscale hqQbound
    calc
      _ = |(u p - u P) + (u P - u Q) + (u Q - epsilon * u (reflect q))| := by
        congr 1
        ring
      _ ≤ |u p - u P| + |u P - u Q| + |u Q - epsilon * u (reflect q)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  intro x hx y hy
  by_cases hx0 : 0 ≤ x 0
  · by_cases hy0 : 0 ≤ y 0
    · simp only [m64ContinuousBoundaryReflect, if_pos hx0, if_pos hy0]
      exact (hholder x hx hx0 y hy hy0).trans (hcost x y)
    · simp only [m64ContinuousBoundaryReflect, if_pos hx0, if_neg hy0]
      exact hmixed x hx hx0 y hy (le_of_not_ge hy0)
  · by_cases hy0 : 0 ≤ y 0
    · simp only [m64ContinuousBoundaryReflect, if_neg hx0, if_pos hy0]
      simpa only [abs_sub_comm, norm_sub_rev] using
        hmixed y hy hy0 x hx (le_of_not_ge hx0)
    · simp only [m64ContinuousBoundaryReflect, if_neg hx0, if_neg hy0,
        ← mul_sub, abs_mul, habs, one_mul]
      have h := hholder (reflect x) (hrball x hx)
        (by rw [reflect_apply_zero]; linarith) (reflect y) (hrball y hy)
        (by rw [reflect_apply_zero]; linarith)
      rw [← map_sub, LinearIsometryEquiv.norm_map] at h
      exact h.trans (hcost x y)

end PoincareConjecture
