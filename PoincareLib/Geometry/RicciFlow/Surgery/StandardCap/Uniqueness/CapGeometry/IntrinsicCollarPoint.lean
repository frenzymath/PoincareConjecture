import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.IntrinsicRadialDistance
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.RadialIntervals

/-!
# Actual points realizing every bounded intrinsic radial offset

Morgan-Tian Theorem 12.32, pp. 326-327. A genuine radial segment has
length equal to its arclength difference. Rotation of that segment
places every prescribed positive radius inside the actual ambient ball
at an arbitrary center, with no angular-distance estimate required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.M35.Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single (2 : Fin 3) 1

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

include hrotation hcomplete

/-- Theorem 12.32: the actual axis segment controls either direction
of change in the genuine radial coordinate. -/
theorem intrinsic_axis_segment_edist_le (a b : ℝ) :
    g.edist ((radialArclengthOrderIso g hrotation hcomplete).symm a • e2)
      ((radialArclengthOrderIso g hrotation hcomplete).symm b • e2) ≤
        ENNReal.ofReal |b - a| := by
  let R := radialArclengthOrderIso g hrotation hcomplete
  rcases le_total a b with hab | hba
  · have h := edist_axis_segment_le g (R.symm.monotone hab)
    change g.edist (R.symm a • e2) (R.symm b • e2) ≤
      ENNReal.ofReal (R (R.symm b) - R (R.symm a)) at h
    simpa only [OrderIso.apply_symm_apply, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  · have h := edist_axis_segment_le g (R.symm.monotone hba)
    change g.edist (R.symm b • e2) (R.symm a • e2) ≤
      ENNReal.ofReal (R (R.symm a) - R (R.symm b)) at h
    rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply] at h
    have hc : g.edist (R.symm a • e2) (R.symm b • e2) =
        g.edist (R.symm b • e2) (R.symm a • e2) :=
      @edist_comm StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace _ _
    rw [hc, abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact h

/-- Theorem 12.32: every positive radial coordinate is represented
along the actual ray through the center, within its arclength difference. -/
theorem exists_intrinsic_collar_point (P : M35StandardCapPredecessors)
    (x : StandardCapSpace) {s : ℝ} (hs : 0 < s) :
    ∃ y : StandardCapSpace, radialArclength g ‖y‖ = s ∧
      g.edist x y ≤ ENNReal.ofReal |s - radialArclength g ‖x‖| := by
  let R := radialArclengthOrderIso g hrotation hcomplete
  obtain ⟨A, hA⟩ := exists_axis_rotation x
  let F := standardRotationDiffeomorph A
  have hmetric : MetricHomothety g g F 1 := by
    intro z u v
    change g.inner (standardRotation A z)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) z u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) z v) = 1 * g.inner z u v
    simpa only [one_mul] using hrotation A z u v
  have H := P.metric_homothety StandardCapSpace StandardCapSpace g g F 1
    zero_lt_one hmetric
  let y := F (R.symm s • e2)
  have hnorm : ‖y‖ = R.symm s := by
    have h := standardRotation_inner A (R.symm s • e2) (R.symm s • e2)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    have hr : 0 < R.symm s := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
    have he : ‖R.symm s • e2‖ = R.symm s := by
      simp [norm_smul, abs_of_pos hr, e2]
    rw [he] at h
    change ‖y‖ ^ 2 = R.symm s ^ 2 at h
    nlinarith only [h, norm_nonneg y, hr]
  refine ⟨y, ?_, ?_⟩
  · rw [hnorm]
    exact R.apply_symm_apply s
  · have hd := H.edist_eq (‖x‖ • e2) (R.symm s • e2)
    have hx : F (‖x‖ • e2) = x := hA
    rw [hx, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hd
    rw [hd]
    have h := intrinsic_axis_segment_edist_le g hrotation hcomplete (R ‖x‖) s
    change g.edist (R.symm (R ‖x‖) • e2) (R.symm s • e2) ≤
      ENNReal.ofReal |s - R ‖x‖| at h
    rw [R.symm_apply_apply] at h
    exact h

end PoincareMT.M35.Uniqueness
