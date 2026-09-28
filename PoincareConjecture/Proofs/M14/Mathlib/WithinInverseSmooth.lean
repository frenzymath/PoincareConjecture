import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M14

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem contDiffOn_inverse_of_leftInverse {f : E → F} {g : F → E}
    {S : Set E} {T : Set F} (hS : UniqueDiffOn 𝕜 S)
    (hf : ContDiffOn 𝕜 ∞ f S) (hg : ContinuousOn g T)
    (hmap : MapsTo g T S) (hfg : ∀ y ∈ T, f (g y) = y)
    (hinv : ∀ z ∈ S, (fderivWithin 𝕜 f S z).IsInvertible) :
    ContDiffOn 𝕜 ∞ g T := by
  let D : F → F →L[𝕜] E := fun y =>
    ContinuousLinearMap.inverse (fderivWithin 𝕜 f S (g y))
  have hD (y : F) (hy : y ∈ T) : HasFDerivWithinAt g (D y) T y := by
    obtain ⟨e, he⟩ := hinv (g y) (hmap hy)
    have hfe : HasFDerivWithinAt f (e : E →L[𝕜] F) S (g y) := by
      rw [he]
      exact (hf.differentiableOn (by simp) _ (hmap hy)).hasFDerivWithinAt
    have hd := HasFDerivWithinAt.of_local_left_inverse
      ((hg y hy).tendsto_nhdsWithin hmap) hfe hy
      (eventually_nhdsWithin_of_forall hfg)
    simpa only [D, ← he, ContinuousLinearMap.inverse_equiv] using hd
  rw [contDiffOn_infty]
  intro k
  induction k with
  | zero => exact contDiffOn_zero.mpr hg
  | succ k ih =>
    have hf' : ContDiffOn 𝕜 k (fderivWithin 𝕜 f S) S :=
      hf.fderivWithin hS (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤))
    have hDs : ContDiffOn 𝕜 k D T := by
      intro y hy
      exact (hinv (g y) (hmap hy)).contDiffAt_map_inverse.comp_contDiffWithinAt y
        ((hf' (g y) (hmap hy)).comp y (ih y hy) hmap)
    rw [Nat.cast_succ]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt (by simp)).mpr
    intro y hy
    refine ⟨T, ?_, by simp, D, hD, hDs⟩
    simpa only [insert_eq_of_mem hy] using (self_mem_nhdsWithin : T ∈ 𝓝[T] y)

end PoincareConjecture.M14
