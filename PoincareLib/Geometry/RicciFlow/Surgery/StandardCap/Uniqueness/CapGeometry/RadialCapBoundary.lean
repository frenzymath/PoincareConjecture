import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.IntrinsicRadialPatch

/-!
# The exact second neck at the actual radial core boundary

Morgan-Tian Theorem 12.32, pp. 326-327, and Definition 9.72. The end
neck and boundary neck are distinct literal radial annuli. The boundary
neck is centered at the end's inner radius, with its own positive speed.
Their actual set identities supply the frozen frontier clause without
changing either requested neck length.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (P : M35StandardCapPredecessors)

include hrotation hcomplete P

/-- Theorem 12.32, pp. 326-327: the second literal radial neck has central
sphere exactly equal to the frontier of the actual closed metric-ball core. -/
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

/-- Theorem 12.32, pp. 326-327: a boundary speed below twice the end speed
keeps the full second neck strictly inside the same actual cap carrier. -/
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

/-- Theorem 12.32, pp. 326-327: every point strictly inside the chosen
actual inner radius belongs to the interior of its literal closed core. -/
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

end PoincareMT.M35.Uniqueness
