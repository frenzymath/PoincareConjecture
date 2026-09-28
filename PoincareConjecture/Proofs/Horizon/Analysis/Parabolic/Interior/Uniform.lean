import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.GlobalEstimate
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.SolutionReduction








open Set
open scoped ContDiff RealInnerProductSpace BigOperators

namespace Poincare.Parabolic.Interior

theorem exists_uniform_interior_heat_hessian_bound
    (n : ℕ) (hn : 1 ≤ n) (lam Λ H : ℝ)
    (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        ContDiffOn ℝ ∞ a (Metric.ball 0 2) →
        (∀ x ∈ Metric.ball 0 2, ∀ v w,
          inner ℝ (a x v) w = inner ℝ v (a x w)) →
        (∀ x ∈ Metric.ball 0 2, ∀ v,
          lam * ‖v‖ ^ 2 ≤ inner ℝ v (a x v) ∧
          inner ℝ v (a x v) ≤ Λ * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 2, ∀ y ∈ Metric.ball 0 2,
          ‖a x - a y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) →
        ∀ (B : ℝ), 0 ≤ B →
        ∀ (f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ),
          ContDiffOn ℝ ∞ f (Metric.ball 0 2 ×ˢ Ioo 0 2) →
          (∀ x ∈ Metric.ball 0 2, ∀ t ∈ Ioc (0 : ℝ) 1,
            HasDerivAt (fun s => f (x, s))
              (∑ i : Fin n, ∑ j : Fin n,
                inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
                  (a x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
                fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x
                  (EuclideanSpace.basisFun (Fin n) ℝ i)
                  (EuclideanSpace.basisFun (Fin n) ℝ j)) t) →
          (∀ x ∈ Metric.ball 0 2, ∀ t ∈ Ioc (0 : ℝ) 1, |f (x, t)| ≤ B) →
          ∀ v w : EuclideanSpace ℝ (Fin n),
            |fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, 1)) y) 0 v w| ≤
              C * B * ‖v‖ * ‖w‖ := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨C, hC, hest⟩ := exists_uniform_global_interior_heat_hessian_bound
    (ι := Fin n) (F := ℝ) lam Λ H hlam hlamΛ hH
  refine ⟨C, hC, ?_⟩
  intro a _ha hsym hell hholder B hB f hf hpde hb v w
  obtain ⟨g, hg, _hgc, _heq, hlocal, hjet⟩ :=
    exists_compact_interior_heat_solution a B f hf hpde hb
  have hball {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.closedBall 0 1) :
      x ∈ Metric.ball 0 2 := lt_of_le_of_lt hx (by norm_num : (1 : ℝ) < 2)
  have hlocal' (p : EuclideanSpace ℝ (Fin n) × ℝ)
      (hp : p ∈ interiorCompactCylinder) :
      |g p| ≤ B ∧ timeDerivative g p = Kernel.matrixLap (coefficientMatrix (a p.1))
        (spatialDerivative (spatialDerivative g) p) := by
    apply hlocal p.1 (hp.1.trans (by norm_num : (1 : ℝ) ≤ 3 / 2)) p.2
    exact ⟨(by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans hp.2.1, hp.2.2⟩
  have he := hest a (fun x hx => hsym x (hball hx))
    (fun x hx => hell x (hball hx))
    (fun x hx y hy => hholder x (hball hx) y (hball hy)) B hB g hg
    (fun p hp => (hlocal' p hp).2) (fun p hp => (hlocal' p hp).1) v w
  rw [hjet] at he
  exact he

end Poincare.Parabolic.Interior
