import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.C2ZeroTraceRegularity
import PoincareConjecture.Proofs.M64.Mathlib.WeakPartialSchwartz















set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff SchwartzMap
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture





theorem m64ZeroTrace_quadratic_contDiffOn {N : ℕ} {R C H beta Lambda : ℝ}
    (hR : 0 < R) (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (hu : MemLp u 2 (volume.restrict (ball (0 : LoopPlane) R)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball (0 : LoopPlane) R)))
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun z => V i z j) (fun z => u z j)
      (ball (0 : LoopPlane) R))
    (hsmooth : ContDiffOn ℝ 2 u (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hc : ContinuousOn u (closedBall (0 : LoopPlane) (R / 2)))
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hbeta : 0 < beta) (hLambda : 0 ≤ Lambda)
    (hholder : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2),
      ∀ z ∈ closedBall (0 : LoopPlane) (R / 2),
      ‖u z - u x‖ ≤ H * dist z x ^ beta)
    (hzero : ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), z 1 = 0 → u z = 0)
    (hgrowth : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ u z (EuclideanSpace.single i 1)‖ ^ 2)
    (hdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4),
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖V i z‖ ^ 2) ≤
        Lambda * r ^ (2 * beta)) :
    ContDiffOn ℝ 1 u (closedBall (0 : LoopPlane) (R / 64) ∩ {z | 0 ≤ z 1}) := by
  let X : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) R) := {
    value := u
    derivative := V
    value_memLp := fun _ _ hK => hu.mono_measure (Measure.restrict_mono_set volume hK)
    derivative_memLp := fun i _ _ hK =>
      (hV i).mono_measure (Measure.restrict_mono_set volume hK)
    weak_derivative := by
      intro phi hcompact hs i j
      have hh := hweak i j phi (phi.smooth ⊤) hcompact hs
      simpa only [neg_neg, mul_comm, EuclideanSpace.basisFun_apply, id_eq] using
        (congrArg Neg.neg hh).symm }
  exact m64C2_zero_trace_quadratic_contDiffOn hR X hsmooth hc
    hC hH hbeta hLambda hholder hzero
    (by simpa only [X, EuclideanSpace.basisFun_apply] using hgrowth) hdecay

end PoincareConjecture
