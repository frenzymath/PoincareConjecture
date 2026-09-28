import PoincareConjecture.Proofs.M10.InitialActionContinuity
import PoincareConjecture.Proofs.M10.MinimizingLifts
import PoincareConjecture.Proofs.M10.ScalarBound
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem corrected_square_action_hasDerivAt (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (C : ℝ) {s : ℝ} (hs : 0 < s) (hmax : s ^ 2 < τmax) :
    HasDerivAt (fun r : ℝ ↦ G.toLExponentialFamily.action Z (r ^ 2) + (2 * C / 3) * r ^ 3)
      (2 * s ^ 2 * ((F.connection (T - s ^ 2)).scalarCurvature (G.gamma Z (s ^ 2)) +
        (F.metric (T - s ^ 2)).inner (G.gamma Z (s ^ 2))
          (curveVelocity (G.gamma Z) (s ^ 2)) (curveVelocity (G.gamma Z) (s ^ 2)) + C)) s := by
  have ha := (G.action_time_derivative Z (s ^ 2) (sq_pos_of_pos hs) hmax).comp s
    (h := fun r : ℝ ↦ r ^ 2)
    (hasDerivAt_pow 2 s)
  have hc := (hasDerivAt_pow 3 s).const_mul (2 * C / 3)
  apply (ha.add hc).congr_deriv
  simp only [backwardLIntegrand, Real.sqrt_sq hs.le]
  ring

theorem normalized_action_lower_bound (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {τ C : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hR : ∀ s ∈ Icc 0 τ, ∀ q : M, -C ≤ (F.connection (T - s)).scalarCurvature q) :
    -C * τ / 3 ≤ G.toLExponentialFamily.action Z τ / (2 * Real.sqrt τ) := by
  let H := fun s : ℝ ↦ G.toLExponentialFamily.action Z (s ^ 2) + (2 * C / 3) * s ^ 3
  let D := fun s : ℝ ↦ 2 * s ^ 2 *
    ((F.connection (T - s ^ 2)).scalarCurvature (G.gamma Z (s ^ 2)) +
      (F.metric (T - s ^ 2)).inner (G.gamma Z (s ^ 2))
        (curveVelocity (G.gamma Z) (s ^ 2)) (curveVelocity (G.gamma Z) (s ^ 2)) + C)
  have hc : ContinuousOn H (Icc 0 (Real.sqrt τ)) := by
    apply ContinuousOn.add _ (by fun_prop)
    apply (action_continuousOn_initial G Z hτ hmax).comp (by fun_prop)
    intro s hs
    exact ⟨sq_nonneg s, by nlinarith [Real.sq_sqrt hτ.le, hs.1, hs.2]⟩
  have hd (s : ℝ) (hs : s ∈ Ioo 0 (Real.sqrt τ)) : HasDerivAt H (D s) s := by
    apply corrected_square_action_hasDerivAt G Z C hs.1
    have hsτ : s ^ 2 ≤ τ := by nlinarith [Real.sq_sqrt hτ.le, hs.1, hs.2]
    exact hsτ.trans_lt hmax
  have hnonneg (s : ℝ) (hs : s ∈ Ioo 0 (Real.sqrt τ)) : 0 ≤ D s := by
    have hsτ : s ^ 2 ∈ Icc 0 τ :=
      ⟨sq_nonneg s, by nlinarith [Real.sq_sqrt hτ.le, hs.1, hs.2]⟩
    have hscalar := hR (s ^ 2) hsτ (G.gamma Z (s ^ 2))
    have hkinetic : 0 ≤ (F.metric (T - s ^ 2)).inner (G.gamma Z (s ^ 2))
        (curveVelocity (G.gamma Z) (s ^ 2)) (curveVelocity (G.gamma Z) (s ^ 2)) := by
      by_cases hv : curveVelocity (n := n) (G.gamma Z) (s ^ 2) = 0
      · rw [hv, map_zero]
      · exact ((F.metric (T - s ^ 2)).pos _ _ hv).le
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s)) (by linarith)
  have hm : MonotoneOn H (Icc 0 (Real.sqrt τ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hc
      (fun s hs ↦ (hd s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt)
      (fun s hs ↦ hnonneg s (by simpa only [interior_Icc] using hs))
  have hzero : H 0 = 0 := by
    simp only [H, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_pow (by omega : (3 : ℕ) ≠ 0),
      LExponentialFamily.action, backwardLLength, intervalIntegral.integral_same,
      mul_zero, add_zero]
  have hend : H (Real.sqrt τ) =
      G.toLExponentialFamily.action Z τ + (2 * C / 3) * τ * Real.sqrt τ := by
    dsimp only [H]
    rw [Real.sq_sqrt hτ.le]
    rw [show (Real.sqrt τ) ^ 3 = τ * Real.sqrt τ by
      rw [pow_succ, Real.sq_sqrt hτ.le]]
    ring
  have hbound := hm (left_mem_Icc.mpr (Real.sqrt_nonneg τ))
    (right_mem_Icc.mpr (Real.sqrt_nonneg τ)) (Real.sqrt_nonneg τ)
  rw [hzero, hend] at hbound
  apply (le_div_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.2 hτ))).mpr
  nlinarith only [hbound]

variable [ConnectedSpace M] [T3Space M]

theorem exists_uniform_reducedLength_lower_bound
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ < τmax → ∀ q : M,
      -C * τ / 3 ≤ reducedLength F T p q τ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_scalarCurvature_bound F hcurvature
  refine ⟨C, hC, ?_⟩
  intro τ hτ hmax q
  obtain ⟨Z, _, _, haction⟩ := exists_minimizing_lift hL G q τ hτ hmax
  rw [haction]
  apply normalized_action_lower_bound G Z hτ hmax
  intro s hs y
  have ht : T - s ∈ Icc (T - τmax) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  exact (abs_le.mp (hbound (T - s) ht y)).1

end PoincareConjecture.M10
