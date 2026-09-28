import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialPatch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (P : M35StandardCapPredecessors)

include hrotation hcomplete P

theorem radial_boundary_neck_frontier (q₀ : UnitTwoSphere) (a b length : ℝ)
    (hb : 0 < b) (hl : 0 < length) (hinner : 0 < a - b * length) :
    frontier (closure (g.ball 0 a)) =
      (intrinsicRadialAnnulusPatch g hrotation hcomplete q₀ a b length
        hb hl hinner).centralSphere := by
  have ha : 0 < a := by nlinarith only [hinner, mul_pos hb hl]
  have hr : 0 < (radialArclengthOrderIso g hrotation hcomplete).symm a := by
    simpa only [radialArclengthOrderIso_symm_zero] using
      (radialArclengthOrderIso g hrotation hcomplete).symm.strictMono ha
  rw [closure_ball_zero_eq_radial_closedBall g hrotation hcomplete P ha,
    frontier_closedBall 0 hr.ne', intrinsicRadialAnnulusPatch_centralSphere]

theorem radial_boundary_neck_subset_outer_ball (q₀ : UnitTwoSphere)
    (a b b' length : ℝ) (hb' : 0 < b') (hl : 0 < length)
    (hinner : 0 < (a - b * length) - b' * length) (hspeed : b' < 2 * b) :
    (intrinsicRadialAnnulusPatch g hrotation hcomplete q₀
      (a - b * length) b' length hb' hl hinner).carrier ⊆ g.ball 0 (a + b * length) := by
  rw [intrinsicRadialAnnulusPatch_carrier]
  intro x hx
  have hs : 0 ≤ radialArclength g ‖x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg x)
  change g.edist 0 x < ENNReal.ofReal (a + b * length)
  rw [edist_zero_eq_radialArclength g hrotation hcomplete P,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs]
  have hwidth := mul_lt_mul_of_pos_right hspeed hl
  linarith only [hx.2, hwidth]

theorem mem_interior_radial_core {s : ℝ} (hs : 0 < s)
    {x : StandardCapSpace} (hx : radialArclength g ‖x‖ < s) :
    x ∈ interior (closure (g.ball 0 s)) := by
  have hr : 0 < (radialArclengthOrderIso g hrotation hcomplete).symm s := by
    simpa only [radialArclengthOrderIso_symm_zero] using
      (radialArclengthOrderIso g hrotation hcomplete).symm.strictMono hs
  rw [closure_ball_zero_eq_radial_closedBall g hrotation hcomplete P hs,
    interior_closedBall 0 hr.ne', mem_ball, dist_zero_right]
  change (radialArclengthOrderIso g hrotation hcomplete) ‖x‖ < s at hx
  have h := (radialArclengthOrderIso g hrotation hcomplete).symm.strictMono hx
  simpa only [OrderIso.symm_apply_apply] using h

end PoincareConjecture.M35.Uniqueness
