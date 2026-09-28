import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]




theorem closedODE_exists_ball_bounds {a b : ℝ} (hab : a < b)
    {U : Set E} (hU : IsOpen U) (V : ℝ × E → E)
    (hV : ContDiffOn ℝ ∞ V (Icc a b ×ˢ U)) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ A L K : ℝ≥0, 0 < A ∧ 0 < L ∧ closedBall x₀ (A : ℝ) ⊆ U ∧
      (∀ t ∈ Icc a b, ∀ x ∈ closedBall x₀ (A : ℝ), ‖V (t, x)‖ ≤ L) ∧
      ∀ t ∈ Icc a b, LipschitzOnWith K (fun x => V (t, x)) (closedBall x₀ (A : ℝ)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  let A : ℝ≥0 := ⟨r / 2, (half_pos hr).le⟩
  have hA : 0 < A := half_pos hr
  have hAU : closedBall x₀ (A : ℝ) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  let D := Icc a b ×ˢ U
  let S := Icc a b ×ˢ closedBall x₀ (A : ℝ)
  have hSD : S ⊆ D := prod_mono Subset.rfl hAU
  have hD : UniqueDiffOn ℝ D := (uniqueDiffOn_Icc hab).prod hU.uniqueDiffOn
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall x₀ (A : ℝ))
  obtain ⟨L₀, hL₀⟩ := hS.exists_bound_of_continuousOn (hV.continuousOn.mono hSD)
  obtain ⟨K₀, hK₀⟩ := hS.exists_bound_of_continuousOn
    ((hV.fderivWithin hD (m := ∞) (by simp)).continuousOn.mono hSD)
  let L : ℝ≥0 := ⟨|L₀| + 1, by positivity⟩
  let K : ℝ≥0 := ⟨|K₀|, abs_nonneg _⟩
  have hbound : ∀ z ∈ S, ‖fderivWithin ℝ V D z‖₊ ≤ K := by
    intro z hz
    exact_mod_cast (hK₀ z hz).trans (le_abs_self K₀)
  have hLip : LipschitzOnWith K V S :=
    Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun z hz => ((hV z (hSD hz)).differentiableWithinAt (by simp)).hasFDerivWithinAt.mono hSD)
      hbound ((convex_Icc a b).prod (convex_closedBall x₀ (A : ℝ)))
  refine ⟨A, L, K, hA, show (0 : ℝ) < |L₀| + 1 by positivity, hAU, ?_, ?_⟩
  · intro t ht x hx
    exact (hL₀ (t, x) ⟨ht, hx⟩).trans
      (show L₀ ≤ |L₀| + 1 by linarith [le_abs_self L₀])
  · intro t ht x hx y hy
    simpa only [Prod.edist_eq, edist_self,
      max_eq_right (show 0 ≤ edist x y from bot_le)] using
        hLip (x := (t, x)) (y := (t, y)) ⟨ht, hx⟩ ⟨ht, hy⟩

end PoincareConjecture.M14
