import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.DifferentiatedEquation




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff
open Poincare.Analysis.Parabolic.WeakRegularity
open Poincare.Analysis.Elliptic.Iteration

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ}

theorem partialDeriv_spatialSlice {f : Spacetime n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x, t)) (i : Fin n) :
    partialDeriv i (fun y => f (y, t)) x = Canonical.spatialDeriv i f (x, t) := by
  have h := (hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)).fderiv
  simpa only [partialDeriv, Canonical.spatialDeriv, Canonical.spatialDirection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, Function.comp_def] using
      congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        A (EuclideanSpace.single i 1)) h

theorem partialDeriv_partialDeriv_spatialSlice {f : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (i j : Fin n) :
    partialDeriv i (partialDeriv j (fun y => f (y, t))) x =
      Canonical.spatialDeriv i (Canonical.spatialDeriv j f) (x, t) := by
  have hd : ContDiff ℝ ∞ (Canonical.spatialDeriv j f) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have heq : partialDeriv j (fun y => f (y, t)) =
      fun y => Canonical.spatialDeriv j f (y, t) := by
    funext y
    exact partialDeriv_spatialSlice (hf.differentiable (by simp) (y, t)) j
  rw [heq]
  exact partialDeriv_spatialSlice (hd.differentiable (by simp) (x, t)) i

end PoincareConjecture.RicciFlow.BackwardCoordinates
