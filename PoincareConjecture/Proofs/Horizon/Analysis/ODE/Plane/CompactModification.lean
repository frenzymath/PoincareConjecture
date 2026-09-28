import PoincareConjecture.Proofs.Horizon.Analysis.Complex.SmoothLogarithm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Isometry

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace Poincare.ODE.Plane

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

theorem exists_nonvanishing_compact_modification
    {V : E2 → E2} (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {K : Set E2} (hK : IsCompact K) :
    ∃ W : E2 → E2, ContDiff ℝ ∞ W ∧ (∀ x, W x ≠ 0) ∧ EqOn W V K ∧
      ∃ (S : Set E2) (v : E2), IsCompact S ∧ ∀ x, x ∉ S → W x = v := by
  let e : E2 ≃L[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv
  let f : E2 → ℂ := fun x => e (V x)
  have hf : ContDiff ℝ ∞ f := e.contDiff.comp hV
  have hfne (x : E2) : f x ≠ 0 := by simpa [f] using hne x
  obtain ⟨L, hL, _, hexp⟩ := Poincare.Complex.exists_contDiff_logarithm hf hfne
    0 (Complex.log (f 0)) (Complex.exp_log (hfne 0))
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let χ : ContDiffBump (0 : E2) := ⟨R, R + 1, hR, by linarith⟩
  let W : E2 → E2 := fun x => e.symm (Complex.exp (χ x • L x))
  refine ⟨W, e.symm.contDiff.comp ((χ.contDiff.smul hL).cexp), ?_, ?_,
    closedBall 0 (R + 1), e.symm 1, isCompact_closedBall _ _, ?_⟩
  · intro x hx
    have : Complex.exp (χ x • L x) = 0 :=
      e.symm.injective (hx.trans (map_zero e.symm).symm)
    exact Complex.exp_ne_zero _ this
  · intro x hx
    have hχ : χ x = 1 := χ.one_of_mem_closedBall
      (by simpa only [mem_closedBall, dist_zero_right] using hKR x hx)
    simp [W, hχ, hexp, f]
  · intro x hx
    have hχ : χ x = 0 := χ.zero_of_le_dist (le_of_lt (lt_of_not_ge hx))
    simp [W, hχ]

end Poincare.ODE.Plane
