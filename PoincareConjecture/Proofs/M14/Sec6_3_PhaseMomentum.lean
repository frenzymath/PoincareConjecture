import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerMomentum










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J C : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x₀ : M)
  (hC : UniqueDiffOn ℝ C) {q P : ℝ → EuclideanSpace ℝ (Fin n)}
  (hmap : MapsTo q C (extChartAt (𝓡 n) x₀).target)
  (hphase : ∀ s ∈ C, HasDerivWithinAt (fun r => (q r, P r))
    (M08.closedChartEulerPhase F T x₀ C s (q s, P s)) C s)

include hC hmap hphase




theorem closedChartPhase_momentum :
    EqOn (fun s => M08.chartMomentumVector (M08.chartActionMetric F T x₀ (s, q s))
      (derivWithin q C s)) P C := by
  intro s hs
  have hd : HasDerivWithinAt q
      (Ring.inverse (M08.chartMetricOperator F T x₀ (s, q s)) (P s)) C s := (hphase s hs).fst
  have hq : derivWithin q C s =
      Ring.inverse (M08.chartMetricOperator F T x₀ (s, q s)) (P s) :=
    hd.derivWithin (hC s hs)
  change M08.chartMetricOperator F T x₀ (s, q s) (derivWithin q C s) = P s
  rw [hq]
  exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A (P s))
    (Ring.mul_inverse_cancel _ (M08.chartMetricOperator_isUnit_of_target F T x₀ (hmap hs)))




theorem closedChartPhase_momentum_equation :
    ∀ s ∈ C, HasDerivWithinAt
      (fun r => M08.chartMomentumVector (M08.chartActionMetric F T x₀ (r, q r))
        (derivWithin q C r))
      (M08.chartForceVector
        (M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x₀).target
          (M08.chartActionMetric F T x₀) (s, q s))
        (M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x₀).target
          (M08.chartActionPotential F T x₀) (s, q s)) (derivWithin q C s)) C s := by
  intro s hs
  have hd : HasDerivWithinAt q
      (Ring.inverse (M08.chartMetricOperator F T x₀ (s, q s)) (P s)) C s := (hphase s hs).fst
  have hq : derivWithin q C s =
      Ring.inverse (M08.chartMetricOperator F T x₀ (s, q s)) (P s) :=
    hd.derivWithin (hC s hs)
  have hP : HasDerivWithinAt P
      (M08.closedChartEulerPhase F T x₀ C s (q s, P s)).2 C s := (hphase s hs).snd
  dsimp only [M08.closedChartEulerPhase] at hP
  rw [← hq] at hP
  exact hP.congr_of_mem (closedChartPhase_momentum F T x₀ hC hmap hphase) hs

end PoincareConjecture.M14
