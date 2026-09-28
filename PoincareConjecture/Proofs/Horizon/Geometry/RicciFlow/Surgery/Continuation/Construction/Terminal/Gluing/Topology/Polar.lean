import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.Boundary
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

def puncturedClosedBallPolar (r : ℝ) (hr : 0 < r) :
    {x : Metric.closedBall (0 : StandardCapSpace) r // x.val ≠ 0} ≃ₜ
      Metric.sphere (0 : StandardCapSpace) r × Ico (0 : ℝ) 1 where
  toFun x :=
    ((homeomorphSphereProd StandardCapSpace r hr ⟨x.val.val, x.property⟩).1,
      ⟨1 - ‖x.val.val‖ / r, by
        have hxle : ‖x.val.val‖ ≤ r := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using x.val.property
        have hxpos : 0 < ‖x.val.val‖ := norm_pos_iff.mpr x.property
        constructor
        · exact sub_nonneg.mpr ((div_le_one hr).mpr hxle)
        · linarith [div_pos hxpos hr]⟩)
  invFun y :=
    ⟨⟨(1 - y.2.val) • y.1.val, by
      have hy : ‖y.1.val‖ = r := by
        simpa only [Metric.mem_sphere, dist_zero_right] using y.1.property
      have ht : 0 < 1 - y.2.val := sub_pos.mpr y.2.property.2
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht, hy]
      nlinarith [y.2.property.1]⟩,
      smul_ne_zero (sub_pos.mpr y.2.property.2).ne'
        (Metric.ne_of_mem_sphere y.1.property hr.ne')⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change (1 - (1 - ‖x.val.val‖ / r)) • (r • ‖x.val.val‖⁻¹ • x.val.val) = x.val.val
    rw [sub_sub_cancel, smul_smul, smul_smul]
    have hn := norm_ne_zero_iff.mpr x.property
    rw [show ‖x.val.val‖ / r * r * ‖x.val.val‖⁻¹ = 1 by field_simp]
    exact one_smul ℝ _
  right_inv y := by
    have hy : ‖y.1.val‖ = r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using y.1.property
    have ht : 0 < 1 - y.2.val := sub_pos.mpr y.2.property.2
    have hn : ‖(1 - y.2.val) • y.1.val‖ = (1 - y.2.val) * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hy]
    apply Prod.ext
    · apply Subtype.ext
      change r • ‖(1 - y.2.val) • y.1.val‖⁻¹ • ((1 - y.2.val) • y.1.val) = y.1.val
      rw [hn, smul_smul, smul_smul]
      rw [show r * ((1 - y.2.val) * r)⁻¹ * (1 - y.2.val) = 1 by
        field_simp]
      exact one_smul ℝ _
    · apply Subtype.ext
      change 1 - ‖(1 - y.2.val) • y.1.val‖ / r = y.2.val
      rw [hn, mul_div_cancel_right₀ _ hr.ne']
      ring
  continuous_toFun := by
    apply Continuous.prodMk
    · apply (homeomorphSphereProd StandardCapSpace r hr).continuous.fst.comp
      exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    · apply Continuous.subtype_mk
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp continuous_fst)

end PoincareConjecture.Surgery.Terminal.Gluing

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem closedCapHomeomorph_eq_tip_iff
    (x : Metric.closedBall (0 : StandardCapSpace) R.capEuclideanRadius) :
    (R.closedCapHomeomorph x).val = R.tip ↔ x.val = 0 := by
  change R.cap_map x.val = R.tip ↔ x.val = 0
  rw [← R.cap_map_tip]
  constructor
  · exact R.cap_left_inverse.injOn (R.capEuclidean_closedBall_subset x.property)
      (R.capEuclidean_closedBall_subset (Metric.mem_closedBall_self R.capEuclideanRadius_pos.le))
  · exact congrArg R.cap_map

def puncturedClosedCapPolar :
    {x : closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) //
      x.val ≠ R.tip} ≃ₜ UnitTwoSphere × Ico (0 : ℝ) 1 :=
  (R.closedCapHomeomorph.subtype (fun x => not_congr (R.closedCapHomeomorph_eq_tip_iff x).symm)).symm.trans
    ((Surgery.Terminal.Gluing.puncturedClosedBallPolar R.capEuclideanRadius R.capEuclideanRadius_pos).trans
      (R.capBoundaryAngles.prodCongr (Homeomorph.refl _)))

@[simp] theorem puncturedClosedCapPolar_symm_val (q : UnitTwoSphere × Ico (0 : ℝ) 1) :
    (R.puncturedClosedCapPolar.symm q).val.val =
      R.cap_map ((1 - q.2.val) • (R.capBoundaryAngles.symm q.1).val) := rfl

theorem puncturedClosedCapPolar_symm_zero (θ : UnitTwoSphere) :
    (R.puncturedClosedCapPolar.symm (θ, ⟨0, by constructor <;> norm_num⟩)).val.val =
      R.collapse (I.neck.coordinate_map (θ, 0)) := by
  rw [R.puncturedClosedCapPolar_symm_val]
  simp only [sub_zero, one_smul]
  have h := R.coordinate_capBoundaryAngles (R.capBoundaryAngles.symm θ)
  rw [R.capBoundaryAngles.apply_symm_apply] at h
  rw [h]
  exact (R.collapse_capBoundaryToCentral (R.capBoundaryAngles.symm θ)).symm

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem tip_mem_closedCap :
    R.tip ∈ closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
  rw [← R.cap_map_tip, ← R.capEuclidean_closedBall_image]
  exact mem_image_of_mem _ (Metric.mem_closedBall_self R.capEuclideanRadius_pos.le)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem collapse_negative_ne_tip {x : M} (hx : x ∈ I.negativeHalf) :
    R.collapse x ≠ R.tip := by
  have hout : R.collapse x ∈
      (closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)))ᶜ :=
    R.cap_exterior.symm ▸ mem_image_of_mem _ hx
  intro he
  exact hout (he ▸ R.tip_mem_closedCap)

end PoincareConjecture.MetricSurgeryResult
