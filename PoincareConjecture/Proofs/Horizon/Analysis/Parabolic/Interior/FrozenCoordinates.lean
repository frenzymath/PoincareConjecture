import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactRepresentation
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.FrozenPositiveDefinite

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff RealInnerProductSpace

namespace Poincare.Parabolic.Interior

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def spatialPullback (L : V ≃L[ℝ] V) (f : V × ℝ → F) (p : V × ℝ) : F :=
  f (L p.1, p.2)

theorem contDiff_spatialPullback (L : V ≃L[ℝ] V) {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (spatialPullback L f) :=
  hf.comp (L.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).contDiff

omit [NormedSpace ℝ F] in
theorem hasCompactSupport_spatialPullback (L : V ≃L[ℝ] V) {f : V × ℝ → F}
    (hf : HasCompactSupport f) : HasCompactSupport (spatialPullback L f) :=
  hf.comp_isClosedEmbedding
    (L.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toHomeomorph.isClosedEmbedding

theorem timeDerivative_spatialPullback (L : V ≃L[ℝ] V) {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (p : V × ℝ) :
    timeDerivative (spatialPullback L f) p = timeDerivative f (L p.1, p.2) := by
  exact (hasDerivAt_timeSlice ((contDiff_spatialPullback L hf).differentiable (by simp))
    p.1 p.2).unique (hasDerivAt_timeSlice (hf.differentiable (by simp)) (L p.1) p.2)

theorem spatialDerivative_spatialPullback (L : V ≃L[ℝ] V) {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (p : V × ℝ) :
    spatialDerivative (spatialPullback L f) p =
      Kernel.precompJet L (spatialDerivative f (L p.1, p.2)) := by
  have h := (hasFDerivAt_spatialSlice (hf.differentiable (by simp)) (L p.1) p.2).comp
    p.1 L.hasFDerivAt
  exact (hasFDerivAt_spatialSlice
    ((contDiff_spatialPullback L hf).differentiable (by simp)) p.1 p.2).unique h

theorem spatialDerivative_spatialDerivative_spatialPullback (L : V ≃L[ℝ] V)
    {f : V × ℝ → F} (hf : ContDiff ℝ ∞ f) (p : V × ℝ) :
    spatialDerivative (spatialDerivative (spatialPullback L f)) p =
      Kernel.pushHess L (spatialDerivative (spatialDerivative f) (L p.1, p.2)) := by
  have houter := (hasFDerivAt_spatialSlice
    ((contDiff_spatialDerivative hf).differentiable (by simp)) (L p.1) p.2).comp
    p.1 L.hasFDerivAt
  have h := (Kernel.precompJet (F := F) L).hasFDerivAt.comp p.1 houter
  have heq : (fun y => spatialDerivative (spatialPullback L f) (y, p.2)) =
      (fun y => Kernel.precompJet L (spatialDerivative f (L y, p.2))) := by
    funext y
    exact spatialDerivative_spatialPullback L hf (y, p.2)
  have hraw := hasFDerivAt_spatialSlice
    ((contDiff_spatialDerivative (contDiff_spatialPullback L hf)).differentiable (by simp))
    p.1 p.2
  rw [heq] at hraw
  exact hraw.unique h

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lapEval_spd_spatialPullback (A : Matrix ι ι ℝ) (hA : A.PosDef)
    {f : EuclideanSpace ℝ ι × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (p : EuclideanSpace ℝ ι × ℝ) :
    Kernel.lapEval (spatialDerivative (spatialDerivative
      (spatialPullback (Kernel.spdSqrtEquiv A hA) f)) p) =
      Kernel.matrixLap A (spatialDerivative (spatialDerivative f)
        (Kernel.spdSqrtEquiv A hA p.1, p.2)) := by
  rw [spatialDerivative_spatialDerivative_spatialPullback _ hf,
    Kernel.lapEval_basis (EuclideanSpace.basisFun ι ℝ)]
  simpa only [Kernel.pushHess_apply, Kernel.factorLap] using
    Kernel.spd_factorLap A hA
      (spatialDerivative (spatialDerivative f) (Kernel.spdSqrtEquiv A hA p.1, p.2))

theorem heatResidual_spd_spatialPullback (A : Matrix ι ι ℝ) (hA : A.PosDef)
    {f : EuclideanSpace ℝ ι × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (p : EuclideanSpace ℝ ι × ℝ) :
    heatResidual (spatialPullback (Kernel.spdSqrtEquiv A hA) f) p =
      timeDerivative f (Kernel.spdSqrtEquiv A hA p.1, p.2) -
        Kernel.matrixLap A (spatialDerivative (spatialDerivative f)
          (Kernel.spdSqrtEquiv A hA p.1, p.2)) := by
  rw [heatResidual, timeDerivative_spatialPullback _ hf, lapEval_spd_spatialPullback A hA hf]

end Matrix

end Poincare.Parabolic.Interior
