import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft








set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

theorem contDiffOn_inverse_of_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {g : F → E} {s : Set E} {t : Set F}
    (f' : E → E →L[ℝ] F)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinv : ∀ x ∈ s, (f' x).IsInvertible)
    (hf' : ContDiffOn ℝ ∞ f' s)
    (hg : ContinuousOn g t) (hgs : MapsTo g t s)
    (hfg : ∀ y ∈ t, f (g y) = y) : ContDiffOn ℝ ∞ g t := by
  have hderiv (y : F) (hy : y ∈ t) :
      HasFDerivWithinAt g (f' (g y)).inverse t y := by
    obtain ⟨e, he⟩ := hinv (g y) (hgs hy)
    rw [← he, ContinuousLinearMap.inverse_equiv]
    apply HasFDerivWithinAt.of_local_left_inverse ((hg y hy).tendsto_nhdsWithin hgs)
      (he ▸ hf (g y) (hgs hy)) hy (eventually_nhdsWithin_of_forall hfg)
  apply contDiffOn_infty.mpr
  intro k
  induction k with
  | zero => exact contDiffOn_zero.mpr hg
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt (by simp)).mpr
    intro y hy
    refine ⟨t, by simpa [insert_eq_of_mem hy] using self_mem_nhdsWithin,
      by simp, fun z => (f' (g z)).inverse, hderiv, ?_⟩
    have hi : ContDiffOn ℝ k
        (fun x => ContinuousLinearMap.inverse (f' x)) s := by
      intro x hx
      obtain ⟨e, he⟩ := hinv x hx
      exact (he ▸ contDiffAt_map_inverse e).comp_contDiffWithinAt x
        (contDiffOn_infty.mp hf' k x hx)
    exact hi.comp ih hgs

theorem contDiffOn_inverse_of_invertible_fderivWithin
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {g : F → E} {s : Set E} {t : Set F}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s)
    (hinv : ∀ x ∈ s, (fderivWithin ℝ f s x).IsInvertible)
    (hg : ContinuousOn g t) (hgs : MapsTo g t s)
    (hfg : ∀ y ∈ t, f (g y) = y) : ContDiffOn ℝ ∞ g t := by
  exact contDiffOn_inverse_of_derivative (fderivWithin ℝ f s)
    (fun x hx => (hf.differentiableOn (by simp) x hx).hasFDerivWithinAt)
    hinv (hf.fderivWithin hs (by simp)) hg hgs hfg

end PoincareConjecture
