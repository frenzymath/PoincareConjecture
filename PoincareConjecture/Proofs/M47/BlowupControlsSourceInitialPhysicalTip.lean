import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRetainedAxis











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47



theorem source_initial_physical_tip_distance_upper
    {F : SurgeryFlowData.{u}} {T : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    {A : ℝ} (initial : SurgeryCapInitialComparison F T hT i A)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 A)
    (havoid : initial.chart x ∉ ((F.event T hT).caps i).carrier) :
    (F.metric T).edist ((F.event T hT).caps i).tip (initial.chart x) ≤
      ENNReal.ofReal (F.parameters.h T * (F.standard_initial.cylindrical_end.radius + 5 +
        Real.sqrt (1 + ((F.event T hT).necks i).neck.epsilon) *
          |(((F.event T hT).necks i).neck.coordinate_inverse
            (sourceInitialOldMap initial x)).2|)) := by
  let E := F.event T hT
  let N := (E.necks i).neck
  let R := E.local_result i
  let y := sourceInitialOldMap initial x
  let y0 := N.coordinate_map ((N.coordinate_inverse y).1, 0)
  have hret := source_initial_chart_retention hT i initial hx havoid
  have hy : y ∈ N.region (-N.epsilon⁻¹) 0 := hret.2.2
  have hpre : E.retention.inverse (initial.chart x) ∈ E.regular_limit :=
    E.retained_pre_subset (interior_subset hret.2.1)
  have hlimit : E.limit_identify.inverse y = E.retention.inverse (initial.chart x) :=
    E.limit_identify.left_inverse hpre
  have hpoint : E.local_embed i (R.collapse y) = initial.chart x := by
    rw [E.local_retention i y hy, hlimit]
    exact E.retention.right_inverse (interior_subset hret.1)
  have haxis := source_initial_retained_axis_distance R (N.coordinate_inverse y).1 hy.2
  change R.metric.edist (R.collapse (N.coordinate_map (N.coordinate_inverse y)))
    (R.collapse y0) ≤ ENNReal.ofReal
      (N.scale * Real.sqrt (1 + N.epsilon) * |(N.coordinate_inverse y).2|) at haxis
  rw [M36.neck_coordinate_inverse N hy.1] at haxis
  have hphysical := R.metric.edist_le_mul_of_inner_mfderiv_le (F.metric T)
    ((E.local_embed_smooth i).of_le (by simp)) (by norm_num : (0 : ℝ) < 1)
    (fun p w => by simpa only [one_pow, one_mul] using (E.local_metric i p w w).le)
    (R.collapse y) (R.collapse y0)
  simp only [ENNReal.ofReal_one, one_mul] at hphysical
  rw [hpoint] at hphysical
  have hpath := hphysical.trans haxis
  have hcentral : y0 ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨((N.coordinate_inverse y).1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hfront : R.collapse y0 ∈ frontier (R.cap_map ''
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 4)) := by
    rw [← R.cap_boundary]
    exact mem_image_of_mem R.collapse hcentral
  have hcap : E.local_embed i (R.collapse y0) ∈ (E.caps i).carrier := by
    rw [← E.local_cap_image i]
    exact mem_image_of_mem (E.local_embed i) (frontier_subset_closure hfront)
  have houter := (E.caps i).outer_ball hcap
  have hscale : N.scale = F.parameters.h T := E.neck_scale i
  have hh : 0 < F.parameters.h T := hscale ▸ N.scale_pos
  rw [hscale] at hpath
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice T).carrier → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hreverse : (F.metric T).edist (E.local_embed i (R.collapse y0)) (initial.chart x) =
      (F.metric T).edist (initial.chart x) (E.local_embed i (R.collapse y0)) :=
    Manifold.riemannianEDist_comm
  calc
    (F.metric T).edist (E.caps i).tip (initial.chart x) ≤
        (F.metric T).edist (E.caps i).tip (E.local_embed i (R.collapse y0)) +
          (F.metric T).edist (E.local_embed i (R.collapse y0)) (initial.chart x) :=
      Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (F.parameters.h T * (F.standard_initial.cylindrical_end.radius + 5)) +
        ENNReal.ofReal (F.parameters.h T * Real.sqrt (1 + N.epsilon) *
          |(N.coordinate_inverse y).2|) := by
      rw [hreverse]
      exact add_le_add houter hpath
    _ = _ := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg hh.le (by linarith [F.standard_initial.cylindrical_end.radius_pos]))
        (mul_nonneg (mul_nonneg hh.le (Real.sqrt_nonneg _)) (abs_nonneg _))]
      congr 1
      ring

end PoincareConjecture.M47
