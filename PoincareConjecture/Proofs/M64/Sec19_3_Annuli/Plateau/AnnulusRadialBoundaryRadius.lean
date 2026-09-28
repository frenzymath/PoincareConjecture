import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialBoundaryEnergy












set_option autoImplicit false

open Set MeasureTheory Metric
open scoped ContDiff NNReal

namespace PoincareConjecture

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)



theorem m64Periodic_contDiff_lipschitz {c : ℝ → E}
    (hc : ContDiff ℝ 1 c) (hP : Function.Periodic c curvePeriod) :
    ∃ D : ℝ≥0, LipschitzWith D c := by
  obtain ⟨D, hD, hbound⟩ := m64Periodic_contDiff_deriv_bound hc hP
  exact ⟨⟨D, hD⟩, lipschitzWith_of_nnnorm_deriv_le (hc.differentiable (by simp))
    (fun x => hbound x)⟩



theorem m64RadialBoundaryPlane_radius {c : ℝ → E}
    (hc : ContDiff ℝ 1 c) (hP : Function.Periodic c curvePeriod) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : LoopPlane) (r : ℝ), 0 ≤ r →
      ∀ z ∈ closedBall (0 : LoopPlane) 1,
        dist (c ((a + r • z) 0)) (c (a 0 + r)) ≤ C * r := by
  obtain ⟨D, hD⟩ := m64Periodic_contDiff_lipschitz hc hP
  refine ⟨2 * D, by positivity, ?_⟩
  intro a r hr z hz
  have hn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hcoord : |z 0| ≤ 1 := by
    exact (PiLp.norm_apply_le z 0).trans hn
  have harg : dist ((a + r • z) 0) (a 0 + r) ≤ 2 * r := by
    simp only [Real.dist_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [show a 0 + r * z 0 - (a 0 + r) = r * (z 0 - 1) by ring,
      abs_mul, abs_of_nonneg hr]
    have hsub : |z 0 - 1| ≤ 2 := by
      calc
        _ ≤ |z 0| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ 2 := by norm_num at *; linarith
    nlinarith
  calc
    _ ≤ D * dist ((a + r • z) 0) (a 0 + r) := hD.dist_le_mul _ _
    _ ≤ D * (2 * r) := mul_le_mul_of_nonneg_left harg D.coe_nonneg
    _ = _ := by ring

end PoincareConjecture
