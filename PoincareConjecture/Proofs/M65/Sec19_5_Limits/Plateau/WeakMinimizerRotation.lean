import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryMeasure
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Complex
open scoped Topology

namespace PoincareConjecture

def m65PlaneRotation (θ : ℝ) : LoopPlane ≃ₗᵢ[ℝ] LoopPlane :=
  (orthonormalBasisOneI.repr.symm.trans (rotation (Circle.exp θ))).trans
    orthonormalBasisOneI.repr

private theorem m65Angular_exp (t : ℝ) :
    Proofs.M58.angularPoint t = orthonormalBasisOneI.repr (Circle.exp t : ℂ) := by
  ext i
  fin_cases i <;> simp [Proofs.M58.angularPoint, Circle.coe_exp, Complex.exp_mul_I,
    orthonormalBasisOneI_repr_apply, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem m65PlaneRotation_angular (θ t : ℝ) :
    m65PlaneRotation θ (Proofs.M58.angularPoint t) = Proofs.M58.angularPoint (θ + t) := by
  rw [m65Angular_exp t, m65Angular_exp (θ + t)]
  simp only [m65PlaneRotation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, rotation_apply, Circle.exp_add,
    Circle.coe_mul]

theorem m65PlaneRotation_disk_measurePreserving (θ : ℝ) :
    MeasurePreserving (m65PlaneRotation θ) (volume.restrict loopDiskSet)
      (volume.restrict loopDiskSet) := by
  have hp : (m65PlaneRotation θ) ⁻¹' loopDiskSet = loopDiskSet := by
    ext z
    simp only [mem_preimage, loopDiskSet, mem_closedBall_zero_iff,
      LinearIsometryEquiv.norm_map]
  have h := (m65PlaneRotation θ).measurePreserving.restrict_preimage
    (show MeasurableSet loopDiskSet from Metric.isClosed_closedBall.measurableSet)
  simpa only [hp] using h

private theorem m65Angular_periodic : Function.Periodic Proofs.M58.angularPoint (2 * Real.pi) := by
  intro t
  ext i
  fin_cases i <;> simp [Proofs.M58.angularPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem m65PlaneRotation_boundary_measurePreserving (θ : ℝ) :
    MeasurePreserving (m65PlaneRotation θ) m65CircleBoundaryMeasure m65CircleBoundaryMeasure := by
  let T : ℝ := 2 * Real.pi
  let : Fact (0 < T) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  let f : AddCircle T → LoopPlane := m65Angular_periodic.lift
  have hf : Continuous f := by
    unfold f Function.Periodic.lift
    exact Proofs.M58.contDiff_angularPoint.continuous.quotient_liftOn' _
  have hq : MeasurePreserving (fun t : ℝ => (t : AddCircle T))
      (volume.restrict (Icc (-Real.pi) Real.pi)) volume := by
    have h := AddCircle.measurePreserving_mk T (-Real.pi)
    have he : -Real.pi + T = Real.pi := by dsimp only [T]; ring
    rw [he] at h
    have hm : volume.restrict (Icc (-Real.pi) Real.pi) =
        volume.restrict (Ioc (-Real.pi) Real.pi) :=
      Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
    rw [hm]
    exact h
  have hbase : Measure.map f volume = m65CircleBoundaryMeasure := by
    rw [← hq.map_eq, Measure.map_map hf.measurable hq.measurable]
    rfl
  have hact : (m65PlaneRotation θ) ∘ f = f ∘ (fun s : AddCircle T => (θ : AddCircle T) + s) := by
    funext s
    induction s using Quotient.inductionOn' with
    | h t =>
      change m65PlaneRotation θ (Proofs.M58.angularPoint t) =
        m65Angular_periodic.lift ((θ : AddCircle T) + (t : AddCircle T))
      rw [← AddCircle.coe_add, Function.Periodic.lift_coe]
      exact m65PlaneRotation_angular θ t
  refine ⟨(m65PlaneRotation θ).continuous.measurable, ?_⟩
  rw [← hbase, Measure.map_map (m65PlaneRotation θ).continuous.measurable hf.measurable,
    hact, ← Measure.map_map hf.measurable
      (show Measurable (fun s : AddCircle T => (θ : AddCircle T) + s) from by fun_prop),
    (measurePreserving_add_left (volume : Measure (AddCircle T)) (θ : AddCircle T)).map_eq]

end PoincareConjecture
