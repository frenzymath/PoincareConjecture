import PoincareLib.Topology.Manifold.Surgery.Event.Small.SmallCoordinateMotion
import PoincareLib.Topology.Manifold.Surgery.Event.Ball.BallPatchDiffeomorph
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Small supported point motions in the actual ball coordinates

One fixed smooth bump gives an internally chosen displacement radius.
Every smaller vector defines the literal Euclidean motion
`x + beta(x) * v`, which patches through an actual surgery-ball chart.
The original center and inner coordinate formulas are retained.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff NNReal

universe u

namespace PoincareMT.M38

/-- A fixed compact bump equal to one through radius one half and zero from radius one. -/
noncomputable def coordinateMotionBump : ContDiffBump (0 : StandardCapSpace) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The fixed bump is smooth in the actual Euclidean coordinates. -/
theorem coordinateMotionBump_smooth :
    ContDiff ℝ ∞ (coordinateMotionBump : StandardCapSpace → ℝ) :=
  coordinateMotionBump.contDiff

/-- Every inner-half-ball point has the exact bump value one. -/
theorem coordinateMotionBump_one (x : StandardCapSpace) (hx : ‖x‖ ≤ 1 / 2) :
    coordinateMotionBump x = 1 :=
  coordinateMotionBump.one_of_mem_closedBall (by
    simpa only [coordinateMotionBump, Metric.mem_closedBall, dist_zero_right] using hx)

/-- Every point from radius one outward has the exact bump value zero. -/
theorem coordinateMotionBump_zero (x : StandardCapSpace) (hx : 1 ≤ ‖x‖) :
    coordinateMotionBump x = 0 :=
  coordinateMotionBump.zero_of_le_dist (by
    simpa only [coordinateMotionBump, dist_zero_right] using hx)

/-- Smoothness and compact support supply a finite global Lipschitz bound for this same bump. -/
theorem coordinateMotionBump_exists_lipschitz :
    ∃ K : ℝ≥0, LipschitzWith K (coordinateMotionBump : StandardCapSpace → ℝ) :=
  ContDiff.lipschitzWith_of_hasCompactSupport coordinateMotionBump.hasCompactSupport
    coordinateMotionBump_smooth (by simp)

/-- Choose a bound only for the already fixed bump. -/
noncomputable def coordinateMotionBumpConstant : ℝ≥0 :=
  Classical.choose coordinateMotionBump_exists_lipschitz

/-- The selected bound controls the actual bump function. -/
theorem coordinateMotionBump_lipschitz :
    LipschitzWith coordinateMotionBumpConstant (coordinateMotionBump : StandardCapSpace → ℝ) :=
  Classical.choose_spec coordinateMotionBump_exists_lipschitz

/-- A positive coordinate displacement radius derived only from the fixed bump bound. -/
noncomputable def coordinateMotionRadius : ℝ :=
  min (1 / 4) (1 / (2 * ((coordinateMotionBumpConstant : ℝ) + 1)))

/-- The displacement radius remains positive even if the selected Lipschitz bound is zero. -/
theorem coordinateMotionRadius_pos : 0 < coordinateMotionRadius := by
  unfold coordinateMotionRadius
  apply lt_min (by norm_num)
  positivity

/-- Every permitted displacement is less than one quarter in the original Euclidean norm. -/
theorem coordinateMotionRadius_le : coordinateMotionRadius ≤ 1 / 4 := min_le_left _ _

/-- The supported perturbation uses the exact fixed bump and the given vector. -/
noncomputable def coordinateMotionPerturbation (v x : StandardCapSpace) : StandardCapSpace :=
  coordinateMotionBump x • v

/-- Multiplying the fixed scalar bump by the given vector is smooth. -/
theorem coordinateMotionPerturbation_smooth (v : StandardCapSpace) :
    ContDiff ℝ ∞ (coordinateMotionPerturbation v) :=
  coordinateMotionBump_smooth.smul contDiff_const

/-- The perturbation's Lipschitz bound is the bump bound times the actual displacement norm. -/
theorem coordinateMotionPerturbation_lipschitz (v : StandardCapSpace) :
    LipschitzWith (coordinateMotionBumpConstant * ‖v‖₊) (coordinateMotionPerturbation v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := coordinateMotionBump_lipschitz.dist_le_mul x y
  simp only [dist_eq_norm, Real.norm_eq_abs] at hb
  calc
    dist (coordinateMotionPerturbation v x) (coordinateMotionPerturbation v y) =
        |coordinateMotionBump x - coordinateMotionBump y| * ‖v‖ := by
      change dist (coordinateMotionBump x • v) (coordinateMotionBump y • v) = _
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    _ ≤ ((coordinateMotionBumpConstant : ℝ) * ‖x - y‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg v)
    _ = (coordinateMotionBumpConstant * ‖v‖₊ : ℝ≥0) * dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm]
      ring

/-- The internally chosen displacement radius makes that perturbation strictly small. -/
theorem coordinateMotionPerturbation_small (v : StandardCapSpace)
    (hv : ‖v‖ < coordinateMotionRadius) : coordinateMotionBumpConstant * ‖v‖₊ < 1 := by
  have hden : 0 < 2 * ((coordinateMotionBumpConstant : ℝ) + 1) := by positivity
  have hv' : ‖v‖ < 1 / (2 * ((coordinateMotionBumpConstant : ℝ) + 1)) :=
    hv.trans_le (min_le_right _ _)
  have hproduct := (lt_div_iff₀ hden).mp hv'
  have hnorm : 0 ≤ ‖v‖ := norm_nonneg v
  have hK : 0 ≤ (coordinateMotionBumpConstant : ℝ) := coordinateMotionBumpConstant.property
  have hstrict : (coordinateMotionBumpConstant : ℝ) * ‖v‖ < 1 := by nlinarith
  exact_mod_cast hstrict

/-- The owner's small-perturbation theorem supplies a diffeomorphism with these actual maps. -/
noncomputable def coordinatePointMotion (v : StandardCapSpace)
    (hv : ‖v‖ < coordinateMotionRadius) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
  smallCoordinateDiffeomorph (coordinateMotionPerturbation v)
    (coordinateMotionPerturbation_lipschitz v) (coordinateMotionPerturbation_small v hv)
    (coordinateMotionPerturbation_smooth v)

/-- The constructed Euclidean motion has exactly the original bump-translation formula. -/
theorem coordinatePointMotion_apply (v : StandardCapSpace) (hv : ‖v‖ < coordinateMotionRadius)
    (x : StandardCapSpace) :
    coordinatePointMotion v hv x = x + coordinateMotionBump x • v := rfl

/-- On the whole inner half ball the motion is precisely translation by v. -/
theorem coordinatePointMotion_inner (v : StandardCapSpace) (hv : ‖v‖ < coordinateMotionRadius)
    (x : StandardCapSpace) (hx : ‖x‖ ≤ 1 / 2) :
    coordinatePointMotion v hv x = x + v := by
  rw [coordinatePointMotion_apply, coordinateMotionBump_one x hx, one_smul]

/-- In particular, the actual Euclidean center is sent to the given vector. -/
theorem coordinatePointMotion_zero (v : StandardCapSpace) (hv : ‖v‖ < coordinateMotionRadius) :
    coordinatePointMotion v hv 0 = v := by
  simpa only [zero_add] using coordinatePointMotion_inner v hv 0 (by simp)

/-- Every point from radius one onward is fixed by the same motion. -/
theorem coordinatePointMotion_outer (v : StandardCapSpace) (hv : ‖v‖ < coordinateMotionRadius)
    (x : StandardCapSpace) (hx : 1 ≤ ‖x‖) : coordinatePointMotion v hv x = x := by
  rw [coordinatePointMotion_apply, coordinateMotionBump_zero x hx, zero_smul, add_zero]

/-- The whole outer region required by the actual ball-patching lemma is fixed. -/
theorem coordinatePointMotion_patch_outer (v : StandardCapSpace)
    (hv : ‖v‖ < coordinateMotionRadius) (x : StandardCapSpace) (hx : 3 / 2 ≤ ‖x‖) :
    coordinatePointMotion v hv x = x :=
  coordinatePointMotion_outer v hv x (by linarith)

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

/-- Patch the same actual coordinate motion into the original ball embedding. -/
noncomputable def surgeryBallPointMotion (v : StandardCapSpace)
    (hv : ‖v‖ < coordinateMotionRadius) :
    Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞ :=
  surgeryBallPatchDiffeomorph (coordinatePointMotion v hv)
    (coordinatePointMotion_patch_outer v hv) B

/-- The total ambient map is literally the existing patch of the chosen coordinate motion. -/
theorem surgeryBallPointMotion_apply (v : StandardCapSpace) (hv : ‖v‖ < coordinateMotionRadius)
    (x : A.carrier) :
    surgeryBallPointMotion B v hv x = surgeryBallPatch B (coordinatePointMotion v hv) x := rfl

/-- The total ambient inverse is literally the patch of that same coordinate inverse. -/
theorem surgeryBallPointMotion_symm_apply (v : StandardCapSpace)
    (hv : ‖v‖ < coordinateMotionRadius) (x : A.carrier) :
    (surgeryBallPointMotion B v hv).symm x =
      surgeryBallPatch B (coordinatePointMotion v hv).symm x := rfl

/-- Every valid ball coordinate retains the exact bump-translation formula. -/
theorem surgeryBallPointMotion_map (v : StandardCapSpace) (hv : ‖v‖ < coordinateMotionRadius)
    (x : StandardCapSpace) (hx : x ∈ Metric.ball 0 2) :
    surgeryBallPointMotion B v hv (B.map x) = B.map (x + coordinateMotionBump x • v) := by
  rw [surgeryBallPointMotion_apply,
    surgeryBallPatch_of_mem B (coordinatePointMotion v hv) (Set.mem_image_of_mem B.map hx),
    B.left_inverse hx, coordinatePointMotion_apply]

/-- The entire original inner half ball retains the literal translation coordinates. -/
theorem surgeryBallPointMotion_inner (v : StandardCapSpace) (hv : ‖v‖ < coordinateMotionRadius)
    (x : StandardCapSpace) (hx : ‖x‖ ≤ 1 / 2) :
    surgeryBallPointMotion B v hv (B.map x) = B.map (x + v) := by
  have hxball : x ∈ Metric.ball 0 2 := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  rw [surgeryBallPointMotion_map B v hv x hxball, coordinateMotionBump_one x hx, one_smul]

/-- The actual ambient ball center moves to the point with the prescribed small coordinate. -/
theorem surgeryBallPointMotion_center (v : StandardCapSpace)
    (hv : ‖v‖ < coordinateMotionRadius) :
    surgeryBallPointMotion B v hv (B.map 0) = B.map v := by
  simpa only [zero_add] using surgeryBallPointMotion_inner B v hv 0 (by simp)

/-- The actual ambient motion fixes the complement of the same compact smaller ball image. -/
theorem surgeryBallPointMotion_eq_self_off_compact (v : StandardCapSpace)
    (hv : ‖v‖ < coordinateMotionRadius) {x : A.carrier}
    (hx : x ∉ B.map '' Metric.closedBall 0 (3 / 2)) :
    surgeryBallPointMotion B v hv x = x :=
  surgeryBallPatchDiffeomorph_eq_self_off_compact _ _ B hx

/-- The actual ambient inverse fixes that compact-image complement as well. -/
theorem surgeryBallPointMotion_symm_eq_self_off_compact (v : StandardCapSpace)
    (hv : ‖v‖ < coordinateMotionRadius) {x : A.carrier}
    (hx : x ∉ B.map '' Metric.closedBall 0 (3 / 2)) :
    (surgeryBallPointMotion B v hv).symm x = x :=
  surgeryBallPatchDiffeomorph_symm_eq_self_off_compact _ _ B hx

/-- Every actual ball chart admits a positive range of supported center motions.
The bound comes from the fixed bump and is not a hypothesis on the flow or its topology. -/
theorem exists_surgeryBallCenterMotion :
    ∃ r : ℝ, 0 < r ∧ ∀ v : StandardCapSpace, ‖v‖ < r →
      ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
        e (B.map 0) = B.map v ∧
          ∀ x : A.carrier, x ∉ B.map '' Metric.ball 0 2 → e x = x := by
  refine ⟨coordinateMotionRadius, coordinateMotionRadius_pos, ?_⟩
  intro v hv
  refine ⟨surgeryBallPointMotion B v hv, surgeryBallPointMotion_center B v hv, ?_⟩
  intro x hx
  apply surgeryBallPointMotion_eq_self_off_compact B v hv
  intro hcompact
  exact hx ((Set.image_mono (Metric.closedBall_subset_ball (by norm_num : (3 / 2 : ℝ) < 2)))
    hcompact)

end PoincareMT.M38
