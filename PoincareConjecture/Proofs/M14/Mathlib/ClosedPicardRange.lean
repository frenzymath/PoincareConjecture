import PoincareConjecture.Proofs.M14.Mathlib.ClosedODEUniqueness

set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_closedPicard_solution_in_ball
    {f : ℝ → E → E} {a b : ℝ} {t₀ : Icc a b} {x₀ x : E} {A r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ A r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ MapsTo α (Icc a b) (closedBall x₀ A) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, fun _ _ => α.compProj_mem_closedBall hf.mul_max_le, ?_⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply ODE.hasDerivWithinAt_picard_Icc t₀.property hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

theorem exists_closedPicard_family_in_domain
    {f : ℝ → E → E} {a b : ℝ} (hab : a < b) {t₀ : Icc a b}
    {x₀ : E} {A r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ A r L K)
    {U : Set E} (hU : IsOpen U) (hball : closedBall x₀ A ⊆ U)
    (hsm : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ U)) :
    ∃ α : E × ℝ → E, ContinuousOn α (closedBall x₀ r ×ˢ Icc a b) ∧
      ∀ x ∈ closedBall x₀ r, α (x, t₀) = x ∧
        MapsTo (fun t => α (x, t)) (Icc a b) U ∧
        ContDiffOn ℝ ∞ (fun t => α (x, t)) (Icc a b) ∧
        ∀ t ∈ Icc a b,
          HasDerivWithinAt (fun s => α (x, s)) (f t (α (x, t))) (Icc a b) t := by
  obtain ⟨α, hα, hc⟩ := hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨α, hc, ?_⟩
  intro x hx
  obtain ⟨β, hβ₀, hβmap, hβ⟩ := exists_closedPicard_solution_in_ball hf hx
  have hmap : MapsTo β (Icc a b) U := fun t ht => hball (hβmap ht)
  have heq := closedODE_interval_solution_unique hab hU (Function.uncurry f) hsm hmap
    hβ (hα x hx).2 t₀.property (hβ₀.trans (hα x hx).1.symm)
  have hαmap : MapsTo (fun t => α (x, t)) (Icc a b) U := by
    intro t ht
    rw [← heq ht]
    exact hmap ht
  exact ⟨(hα x hx).1, hαmap,
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) hsm (hα x hx).2 hαmap,
    (hα x hx).2⟩

end PoincareConjecture.M14
