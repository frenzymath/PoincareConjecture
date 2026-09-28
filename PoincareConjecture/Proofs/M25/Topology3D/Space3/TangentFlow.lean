import PoincareConjecture.Proofs.M25.Topology3D.Space3.InwardFlow

set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

theorem boundedFlow_negField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L) (x : E) (t : ℝ) :
    boundedFlow (fun y => -f y) hK.neg (fun y => by simpa only [norm_neg] using hL y) x t =
      boundedFlow f hK hL x (-t) := by
  have hd (s : ℝ) : HasDerivAt (fun v => boundedFlow f hK hL x (-v))
      (-f (boundedFlow f hK hL x (-s))) s := by
    simpa only [Function.comp_def, neg_one_smul] using
      (boundedFlow_hasDerivAt f hK hL x (-s)).scomp s (hasDerivAt_neg s)
  have heq := boundedField_solution_unique (fun y => -f y) hK.neg
    (boundedFlow_hasDerivAt (fun y => -f y) hK.neg
      (fun y => by simpa only [norm_neg] using hL y) x) hd
    (by simp only [boundedFlow_zero, neg_zero])
  exact congrFun heq t

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem tangentFlow_mapsTo_closedBall (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (htan : ∀ q : E, ‖q‖ = 1 → ⟪q, f q⟫_ℝ = 0) (t : ℝ) :
    MapsTo (fun x => boundedFlow f hK hL x t) (closedBall 0 1) (closedBall 0 1) := by
  by_cases ht : 0 ≤ t
  · exact boundedFlow_mapsTo_closedBall f hK hL (fun q hq => (htan q hq).le) t ht
  · intro x hx
    have hm := boundedFlow_mapsTo_closedBall (fun y => -f y) hK.neg
      (fun y => by simpa only [norm_neg] using hL y)
      (fun q hq => by simp only [inner_neg_right, htan q hq, neg_zero, le_refl])
      (-t) (by linarith) hx
    have hrev := boundedFlow_negField f hK hL x (-t)
    rw [neg_neg] at hrev
    change boundedFlow f hK hL x t ∈ closedBall 0 1
    rw [← hrev]
    exact hm

theorem tangentFlow_image_closedBall (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (htan : ∀ q : E, ‖q‖ = 1 → ⟪q, f q⟫_ℝ = 0) (t : ℝ) :
    (fun x => boundedFlow f hK hL x t) '' closedBall 0 1 = closedBall 0 1 := by
  apply Subset.antisymm (image_subset_iff.mpr (tangentFlow_mapsTo_closedBall f hK hL htan t))
  intro y hy
  refine ⟨boundedFlow f hK hL y (-t), tangentFlow_mapsTo_closedBall f hK hL htan (-t) hy, ?_⟩
  simpa only [neg_neg] using boundedFlow_neg f hK hL y (-t)

end PoincareConjecture.M25.Topology3D
