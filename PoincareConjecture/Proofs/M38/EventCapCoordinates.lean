import PoincareConjecture.Proofs.M38.CapAttachment









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]



structure EventCapCoordinates (i : Fin (F.event T hT).cap_count) where
  radius : ℝ
  width : ℝ
  radius_pos : 0 < radius
  width_pos : 0 < width
  width_lt : width < radius
  intrinsic_ball : F.standard_initial.metric.ball 0
    (F.standard_initial.cylindrical_end.radius + 4) = Metric.ball 0 radius
  ball_domain : Metric.ball (0 : StandardCapSpace) (radius + width) ⊆
    F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5)
  shell_domain : {x : StandardCapSpace | radius - width < ‖x‖ ∧ ‖x‖ < radius + width} ⊆
    F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5) ∩
      ((F.event T hT).local_result i).cap_map ⁻¹'
        (((F.event T hT).local_result i).collapse ''
          ((F.event T hT).necks i).neck.region (-((F.event T hT).necks i).neck.epsilon⁻¹) 1)
  cap_image : (F.event T hT).local_embed i ''
    (((F.event T hT).local_result i).cap_map '' Metric.closedBall 0 radius) =
      ((F.event T hT).caps i).carrier



theorem exists_event_cap_coordinates (i : Fin (F.event T hT).cap_count) :
    Nonempty (EventCapCoordinates F T hT i) := by
  obtain ⟨r, hr, hball, hcap⟩ := event_cap_euclidean_radius F T hT i
  obtain ⟨c, hc, hcr, hdom, hshell⟩ :=
    exists_local_cap_collar_width ((F.event T hT).local_result i) hr hball
  exact ⟨⟨r, c, hr, hc, hcr, hball, hdom, hshell, hcap⟩⟩

namespace EventCapCoordinates

variable {F T hT} {i : Fin (F.event T hT).cap_count}
  (P : EventCapCoordinates F T hT i)


noncomputable def ball : SurgeryBallEmbedding (F.slice T) :=
  eventCapBall F T hT i P.radius P.width P.width_pos P.width_lt P.ball_domain


theorem ball_closedBall : P.ball.closedBall = ((F.event T hT).caps i).carrier :=
  eventCapBall_closedBall F T hT i P.radius P.width P.width_pos P.width_lt
    P.ball_domain P.cap_image


noncomputable def collar : RoundCylinderSpace → (F.slice (F.event T hT).tMinus).carrier :=
  eventCapCollar F T hT i P.radius P.width


noncomputable def collarInverse : (F.slice (F.event T hT).tMinus).carrier → RoundCylinderSpace :=
  eventCapCollarInverse F T hT i P.radius P.width



noncomputable def collarChart :
    OpenPartialHomeomorph RoundCylinderSpace (F.slice (F.event T hT).tMinus).carrier where
  toFun := P.collar
  invFun := P.collarInverse
  source := Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1
  target := P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  map_source' := fun z hz => Set.mem_image_of_mem _ hz
  map_target' := by
    rintro x ⟨z, hz, rfl⟩
    change eventCapCollarInverse F T hT i P.radius P.width
      (eventCapCollar F T hT i P.radius P.width z) ∈ _
    rw [event_cap_collar_left_inverse F T hT i P.width_pos P.width_lt P.shell_domain hz]
    exact hz
  left_inv' := event_cap_collar_left_inverse F T hT i P.width_pos P.width_lt P.shell_domain
  right_inv' := event_cap_collar_right_inverse F T hT i P.width_pos P.width_lt P.shell_domain
  continuousOn_toFun :=
    (event_cap_collar_smooth F T hT i P.width_pos P.width_lt P.shell_domain).continuousOn
  continuousOn_invFun :=
    (event_cap_collar_inverse_smooth F T hT i P.width_pos P.width_lt P.shell_domain).continuousOn
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := event_cap_collar_open F T hT i P.width_pos P.width_lt P.shell_domain


theorem collar_open_on {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (hsub : U ⊆ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) : IsOpen (P.collar '' U) :=
  P.collarChart.isOpen_image_of_subset_source hU hsub


theorem collar_subset_neck : P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) ⊆
    (F.event T hT).limit_identify.inverse '' ((F.event T hT).necks i).neck.carrier := by
  rintro x ⟨z, hz, rfl⟩
  exact ⟨localCapCollar ((F.event T hT).local_result i) P.radius P.width z,
    (local_cap_collar_mem _ P.width_pos P.width_lt P.shell_domain hz).1, rfl⟩



theorem collars_disjoint {j : Fin (F.event T hT).cap_count}
    (Q : EventCapCoordinates F T hT j) (hij : i ≠ j) :
    Disjoint (P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
      (Q.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
  ((Set.disjoint_image_iff (limit_inverse_injective F T hT)).mpr
    ((F.event T hT).neck_carrier_disjoint i j hij)).mono
      P.collar_subset_neck Q.collar_subset_neck


theorem collar_central : P.collar '' (Set.univ ×ˢ ({0} : Set ℝ)) =
    (F.event T hT).limit_identify.inverse '' ((F.event T hT).necks i).neck.central_sphere :=
  event_cap_collar_central F T hT i P.radius_pos P.width P.intrinsic_ball


theorem negative_gluing (z : UnitTwoSphere) (s : ℝ) (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    P.collar (z, s) = (F.event T hT).retention.inverse (P.ball.map ((1 - s) • z.val)) :=
  event_cap_collar_negative_gluing F T hT i P.width_pos P.width_lt P.shell_domain
    P.intrinsic_ball P.ball_domain z s hs


theorem negative_interior : P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) ⊆
    interior (F.event T hT).retained_pre := by
  have hsub : (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (-1 : ℝ) 0 ⊆
      Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans zero_lt_one⟩
  apply (P.collar_open_on (isOpen_univ.prod isOpen_Ioo) hsub).subset_interior_iff.mpr
  rintro x ⟨⟨z, s⟩, hs, rfl⟩
  exact event_cap_collar_negative_retained F T hT i P.width_pos P.width_lt
    P.shell_domain hs.2 P.intrinsic_ball


theorem positive_disjoint :
    Disjoint (P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) (F.event T hT).retained_pre :=
  event_cap_collar_positive_discarded F T hT i P.width_pos P.width_lt P.shell_domain
    P.intrinsic_ball


theorem attachment_graph_closed :
    IsClosed {q : Metric.ball (0 : StandardCapSpace) 2 × ↥((F.event T hT).retained_preᶜ) |
      1 < ‖q.1.val‖ ∧ P.collar (capAttachCoordinates q.1.val) = q.2.val} :=
  event_cap_attachment_graph_closed F T hT i P.width_pos P.width_lt P.shell_domain
    P.intrinsic_ball

end EventCapCoordinates

end PoincareConjecture.M38
