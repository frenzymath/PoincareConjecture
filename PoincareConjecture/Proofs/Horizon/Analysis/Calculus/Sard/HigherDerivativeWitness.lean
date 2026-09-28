import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp








open Set Function
open scoped ContDiff

namespace Poincare.Analysis

theorem exists_regular_scalar_of_iteratedFDeriv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Set E} {f : E → ℝ} {a : E} {k : ℕ}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (ha : a ∈ V)
    (hzero : iteratedFDeriv ℝ k f a = 0)
    (hne : iteratedFDeriv ℝ (k + 1) f a ≠ 0) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g V ∧ g a = 0 ∧
      Surjective (fderiv ℝ g a) ∧
      ∀ x : E, iteratedFDeriv ℝ k f x = 0 → g x = 0 := by
  have hex : ∃ v : Fin (k + 1) → E, iteratedFDeriv ℝ (k + 1) f a v ≠ 0 := by
    by_contra! h
    apply hne
    ext v
    simpa using h v
  obtain ⟨v, hv⟩ := hex
  let g : E → ℝ := fun x => iteratedFDeriv ℝ k f x (Fin.tail v)
  have hD : ∀ x ∈ V, ContDiffAt ℝ ∞ (iteratedFDeriv ℝ k f) x := by
    intro x hx
    exact ((hf x hx).contDiffAt (hV.mem_nhds hx)).iteratedFDeriv_right
      (by exact_mod_cast (le_top : (⊤ : ℕ∞) + k ≤ ⊤))
  have hg : ContDiffOn ℝ ∞ g V := by
    intro x hx
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℝ
      (Fin.tail v)).contDiff.contDiffAt.comp x (hD x hx)).contDiffWithinAt
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · simp [g, hzero]
  · apply LinearMap.surjective (f := (fderiv ℝ g a).toLinearMap)
    intro hz
    apply hv
    have hd := (hD a ha).differentiableAt (by simp)
    rw [hd.iteratedFDeriv_succ_apply_left']
    change (fderiv ℝ g a).toLinearMap (v 0) = 0
    rw [hz]
    rfl
  · intro x hx
    simp [g, hx]

end Poincare.Analysis
