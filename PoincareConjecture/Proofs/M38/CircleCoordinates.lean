import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

private instance complexCircleDimension : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
private instance euclideanCircleDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩

noncomputable def circleCoordinates :
    Diffeomorph (𝓡 1) (𝓡 1) Circle UnitCircle ∞ where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr z.val, by
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using z.norm_coe⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z.val, by
    apply mem_sphere_zero_iff_norm.mpr
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using z.property⟩
  left_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply z.val)
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply z.val)
  contMDiff_toFun :=
    (Complex.orthonormalBasisOneI.repr.contDiff.contMDiff.comp
      contMDiff_coe_sphere).codRestrict_sphere (fun z => by
        simpa only [Function.comp_apply, Metric.mem_sphere, dist_zero_right,
          LinearIsometryEquiv.norm_map] using z.property)
  contMDiff_invFun :=
    (Complex.orthonormalBasisOneI.repr.symm.contDiff.contMDiff.comp
      contMDiff_coe_sphere).codRestrict_sphere (fun z => by
        simpa only [Function.comp_apply, Metric.mem_sphere, dist_zero_right,
          LinearIsometryEquiv.norm_map] using z.property)

noncomputable def circlePeriodMap (s : ℝ) : UnitCircle :=
  circleCoordinates (Circle.exp (2 * Real.pi * s))

theorem circlePeriodMap_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ circlePeriodMap :=
  circleCoordinates.contMDiff.comp
    (contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff)

theorem circlePeriodMap_eq_iff (s t : ℝ) :
    circlePeriodMap s = circlePeriodMap t ↔ ∃ n : ℤ, s = t + (n : ℝ) := by
  change circleCoordinates (Circle.exp (2 * Real.pi * s)) =
    circleCoordinates (Circle.exp (2 * Real.pi * t)) ↔ _
  have hiff : circleCoordinates (Circle.exp (2 * Real.pi * s)) =
      circleCoordinates (Circle.exp (2 * Real.pi * t)) ↔
        Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) :=
    ⟨fun h => by
      simpa only [Diffeomorph.symm_apply_apply] using congrArg circleCoordinates.symm h,
      congrArg circleCoordinates⟩
  rw [hiff, Circle.exp_eq_exp]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) ?_⟩
    calc
      2 * Real.pi * s = 2 * Real.pi * t + (n : ℝ) * (2 * Real.pi) := hn
      _ = 2 * Real.pi * (t + (n : ℝ)) := by ring
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem circlePeriodMap_surjective : Function.Surjective circlePeriodMap := by
  intro b
  obtain ⟨s, hs⟩ := Circle.exp_surjective (circleCoordinates.symm b)
  refine ⟨s / (2 * Real.pi), ?_⟩
  have hscale : 2 * Real.pi * (s / (2 * Real.pi)) = s := by
    field_simp
  dsimp [circlePeriodMap]
  rw [hscale, hs, Diffeomorph.apply_symm_apply]

noncomputable def circleComplex (b : UnitCircle) : ℂ := (circleCoordinates.symm b).val

theorem circleComplex_smooth : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ circleComplex :=
  contMDiff_coe_sphere.comp circleCoordinates.symm.contMDiff

theorem circleRatio_smooth (b0 : UnitCircle) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun b => circleComplex b / circleComplex b0) := by
  have hdiv : ContDiff ℝ ∞ (fun z : ℂ => z / circleComplex b0) := contDiff_id.div_const _
  exact hdiv.contMDiff.comp circleComplex_smooth

def circleLiftArc (b0 : UnitCircle) : Set UnitCircle :=
  {b | circleComplex b / circleComplex b0 ∈ Complex.slitPlane}

theorem circleLiftArc_open (b0 : UnitCircle) : IsOpen (circleLiftArc b0) :=
  Complex.isOpen_slitPlane.preimage (circleRatio_smooth b0).continuous

theorem circleLiftArc_self (b0 : UnitCircle) : b0 ∈ circleLiftArc b0 := by
  change (circleCoordinates.symm b0 : ℂ) / (circleCoordinates.symm b0 : ℂ) ∈ Complex.slitPlane
  rw [div_self (Circle.coe_ne_zero _)]
  exact Complex.one_mem_slitPlane

noncomputable def circleAngleLift (b0 b : UnitCircle) : ℝ :=
  (Complex.arg (circleComplex b0) +
    (Complex.log (circleComplex b / circleComplex b0)).im) / (2 * Real.pi)

theorem circleAngleLift_spec (b0 b : UnitCircle) :
    circlePeriodMap (circleAngleLift b0 b) = b := by
  have hscale : 2 * Real.pi * circleAngleLift b0 b =
      Complex.arg (circleComplex b0) +
        Complex.arg (circleComplex b / circleComplex b0) := by
    dsimp [circleAngleLift]
    rw [Complex.log_im]
    field_simp
  dsimp [circlePeriodMap]
  rw [hscale, Circle.exp_add]
  have h0 : Circle.exp (Complex.arg (circleComplex b0)) = circleCoordinates.symm b0 :=
    Circle.exp_arg _
  have hb : Circle.exp (Complex.arg (circleComplex b / circleComplex b0)) =
      circleCoordinates.symm b / circleCoordinates.symm b0 := by
    simpa only [Circle.coe_div, circleComplex] using
      (Circle.exp_arg (circleCoordinates.symm b / circleCoordinates.symm b0))
  rw [h0, hb]
  have hm : circleCoordinates.symm b0 *
      (circleCoordinates.symm b / circleCoordinates.symm b0) = circleCoordinates.symm b := by
    simp
  rw [hm, Diffeomorph.apply_symm_apply]

theorem circleAngleLift_smooth (b0 : UnitCircle) :
    ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ (circleAngleLift b0) (circleLiftArc b0) := by
  intro b hb
  have hlog : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun z => Complex.log (circleComplex z / circleComplex b0)) b :=
    ((Complex.contDiffAt_log hb).restrict_scalars ℝ).contMDiffAt.comp b
      (circleRatio_smooth b0 b)
  have him : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun z => (Complex.log (circleComplex z / circleComplex b0)).im) b :=
    Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp b hlog
  have hscale : ContDiff ℝ ∞ (fun t : ℝ =>
      (Complex.arg (circleComplex b0) + t) / (2 * Real.pi)) :=
    (contDiff_const.add contDiff_id).div_const _
  exact (hscale.contMDiff.contMDiffAt.comp b him).contMDiffWithinAt

end PoincareConjecture.M38
