import PoincareConjecture.Proofs.M09.ExponentialConcatenation
import PoincareConjecture.Proofs.M09.MinimizingInitialVectors

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T2Space M]

theorem lExponentialFamily_minimizing_prefix {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (c b : ℝ) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b (hc.trans hcb) hmax)) :
    IsMinimizingBackwardLPath F T 0 c (A.path Z c hc (hcb.trans hmax)) := by
  have hcmax := hcb.trans hmax
  obtain ⟨W, hWend, hWmin⟩ := lExponentialFamily_exists_minimizing_initialVector
    hM04 hL hτmax hwindow A c hc hcmax (A.gamma Z c)
  have hcompare : A.action Z c ≤ A.action W c := by
    by_contra h
    have hgap : 0 < (A.action Z c - A.action W c) / 2 := by linarith
    obtain ⟨Q, hQ0, hQb, hQaction⟩ := lExponentialFamily_concat_approx
      hM04 hτmax hwindow A A W Z c b hc hcb hmax hWend _ hgap
    have hQ0' : Q.curve 0 = (A.path Z b (hc.trans hcb) hmax).curve 0 := by
      simpa only [A.path_eq, A.gamma_at_zero] using hQ0
    have hQb' : Q.curve b = (A.path Z b (hc.trans hcb) hmax).curve b := by
      simpa only [A.path_eq] using hQb
    have hfull := hmin Q hQ0' hQb'
    rw [A.path_eq] at hfull
    change A.action Z b ≤ backwardLLength F T 0 b Q.curve at hfull
    linarith
  intro P hP0 hPc
  have hP0' : P.curve 0 = (A.path W c hc hcmax).curve 0 := by
    simpa only [A.path_eq, A.gamma_at_zero] using hP0
  have hPc' : P.curve c = (A.path W c hc hcmax).curve c := by
    rw [A.path_eq] at hPc ⊢
    exact hPc.trans hWend.symm
  have hcomp := hWmin P hP0' hPc'
  rw [A.path_eq] at hcomp ⊢
  exact hcompare.trans hcomp

end PoincareConjecture.Proofs.M09
