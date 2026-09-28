import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.Homothety

theorem contDiffOn_leftInverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : F → E} {g : E → F} {s : Set E} {t : Set F}
    (hf : ContDiffOn ℝ ∞ f t) (ht : UniqueDiffOn ℝ t)
    (hg : ContinuousOn g s) (hmap : MapsTo g s t)
    (hfg : ∀ x ∈ s, f (g x) = x)
    (hinv : ∀ x ∈ s, (fderivWithin ℝ f t (g x)).IsInvertible) :
    ContDiffOn ℝ ∞ g s := by
  let G' : E → E →L[ℝ] F := fun x ↦
    ContinuousLinearMap.inverse (fderivWithin ℝ f t (g x))
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt g (G' x) s x := by
    intro x hx
    obtain ⟨e, he⟩ := hinv x hx
    have hdf : HasFDerivWithinAt f (e : F →L[ℝ] E) t (g x) := by
      rw [he]
      exact (hf.differentiableOn (by simp) (g x) (hmap hx)).hasFDerivWithinAt
    have hleft : ∀ᶠ y in 𝓝[s] x, f (g y) = y := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hfg y hy
    have hd := hdf.of_local_left_inverse ((hg x hx).tendsto_nhdsWithin hmap) hx hleft
    simpa only [G', ← he, ContinuousLinearMap.inverse_equiv] using hd
  apply contDiffOn_infty.mpr
  intro k
  induction k with
  | zero => exact contDiffOn_zero.mpr hg
  | succ k ih =>
      have hdf : ContDiffOn ℝ (k : ℕ∞ω)
          (fun x ↦ fderivWithin ℝ f t (g x)) s :=
        (hf.fderivWithin ht
          (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))).comp ih hmap
      intro x hx
      have hG' : ContDiffWithinAt ℝ (k : ℕ∞ω) G' s x := by
        change ContDiffWithinAt ℝ (k : ℕ∞ω)
          (ContinuousLinearMap.inverse ∘ fun x ↦ fderivWithin ℝ f t (g x)) s x
        exact (hinv x hx).contDiffAt_map_inverse.comp_contDiffWithinAt x (hdf x hx)
      rw [Nat.cast_add, Nat.cast_one,
        contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp), insert_eq_of_mem hx]
      exact ⟨s, self_mem_nhdsWithin, (by simp), G', hderiv, hG'⟩

end PoincareConjecture.Homothety
