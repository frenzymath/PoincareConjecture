import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricEntropyTest
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.LinearTailJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem metricEntropyTest_jet_bounds (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (Q : ℝ) (e : V) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x z w, ‖metricEntropyTest g η Q e (x, z) - metricEntropyTest g η Q e (x, w)‖ ≤
        C * ‖z - w‖) ∧
      (∀ j : Fin n, ∀ x z w,
        ‖nonlinearSpaceJet (metricEntropyTest g η Q e) x z (EuclideanSpace.single j (1 : ℝ)) -
          nonlinearSpaceJet (metricEntropyTest g η Q e) x w (EuclideanSpace.single j (1 : ℝ))‖ ≤
            C * ‖z - w‖) ∧
      (∀ x z, ‖nonlinearValueJet (metricEntropyTest g η Q e) x z‖ ≤ C) ∧
      (∀ x z w,
        ‖nonlinearValueJet (metricEntropyTest g η Q e) x z -
          nonlinearValueJet (metricEntropyTest g η Q e) x w‖ ≤ C * ‖z - w‖) := by
  obtain ⟨C, hC, hLip, hspace, hval, hvalLip⟩ := compact_linear_tail_jet_bounds
    (metricEntropyRemainder_contDiff g hη Q e)
    (metricEntropyRemainder_hasCompactSupport g hc Q e)
    (metricEntropyLinear_contDiff g hη e) (metricEntropyLinear_hasCompactSupport g hc e)
  have he : metricEntropyTest g η Q e = fun p : V × V =>
      metricEntropyRemainder g η Q e p + metricEntropyLinear g η e p.1 p.2 :=
    funext (metricEntropyTest_eq_linear_add g η Q e)
  rw [← he] at hspace hval hvalLip
  refine ⟨C, hC, ?_, ?_, hval, hvalLip⟩
  · simpa only [metricEntropyTest_eq_linear_add] using hLip
  · intro j x z w
    exact hspace x z w (EuclideanSpace.single j 1) (by simp)

end PoincareConjecture.M35.Uniqueness.Heat
