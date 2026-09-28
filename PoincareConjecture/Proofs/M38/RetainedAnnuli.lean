import PoincareConjecture.Proofs.M38.RetentionInterior
import PoincareConjecture.Proofs.M38.CappingComponentLabels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]

def eventCapComplementOpen : TopologicalSpace.Opens (F.slice T).carrier :=
  ⟨(⋃ i, ((F.event T hT).caps i).carrier)ᶜ,
    (isClosed_iUnion_of_finite fun i =>
      ((F.event T hT).caps i).carrier_compact.isClosed).isOpen_compl⟩

namespace EventCapCoordinates

variable {F T hT} {i : Fin (F.event T hT).cap_count}
  (P : EventCapCoordinates F T hT i)

theorem retained_gluing (z : UnitTwoSphere) (s : ℝ)
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    P.ball.map ((1 - s) • z.val) = (F.event T hT).retention.map (P.collar (z, s)) := by
  have hz : (z, s) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Set.mem_univ _, hs.1, hs.2.trans zero_lt_one⟩
  have hneg := local_cap_collar_negative ((F.event T hT).local_result i)
    P.width_pos P.width_lt P.shell_domain (z := z) hs P.intrinsic_ball
    (standard_cap_ball_extended _ P.radius_pos P.intrinsic_ball)
  have hret := (F.event T hT).local_retention i _ hneg
  rw [local_cap_collar_collapse _ P.width_pos P.width_lt P.shell_domain hz] at hret
  have hrad : capRadialDiffeomorph P.radius P.width P.width_pos P.width_lt
      ((1 - s) • z.val) = capShellMap P.radius P.width (z, s) := by
    rw [capRadialDiffeomorph_smul P.width_pos P.width_lt z (1 - s) (by linarith [hs.2])]
    congr 1
    dsimp [capShellMap]
    ring
  change (eventCapBall F T hT i P.radius P.width P.width_pos P.width_lt P.ball_domain).map
    ((1 - s) • z.val) = _
  rw [eventCapBall_map, hrad, hret]
  rfl

theorem ball_annular_mem {x : StandardCapSpace} (hx : 1 < ‖x‖ ∧ ‖x‖ < 2) :
    P.ball.map x ∈ eventCapComplementOpen F T hT := by
  have hs : 1 - ‖x‖ ∈ Set.Ioo (-1 : ℝ) 0 := by
    constructor <;> linarith [hx.1, hx.2]
  have h := P.retained_gluing (capUnitDirection x) (1 - ‖x‖) hs
  rw [show 1 - (1 - ‖x‖) = ‖x‖ by ring, capUnitDirection_radial] at h
  rw [h]
  change _ ∈ (⋃ j, ((F.event T hT).caps j).carrier)ᶜ
  rw [← retention_interior_image]
  exact Set.mem_image_of_mem _ (P.negative_interior
    ⟨(capUnitDirection x, 1 - ‖x‖), ⟨Set.mem_univ _, hs⟩, rfl⟩)

theorem ball_mem_cap_complement_iff {x : StandardCapSpace}
    (hx : x ∈ Metric.ball (0 : StandardCapSpace) 2) :
    P.ball.map x ∈ eventCapComplementOpen F T hT ↔ 1 < ‖x‖ := by
  constructor
  · intro hy
    by_contra h
    have hcap : P.ball.map x ∈ ((F.event T hT).caps i).carrier := by
      rw [← P.ball_closedBall]
      exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_not_gt h, rfl⟩
    exact hy (Set.mem_iUnion.mpr ⟨i, hcap⟩)
  · intro h
    exact P.ball_annular_mem ⟨h, by simpa only [Metric.mem_ball, dist_zero_right] using hx⟩

theorem ball_patch_open : IsOpen (P.ball.map '' Metric.ball (0 : StandardCapSpace) 2) := by
  have h := P.ball.open_embedding.isOpen_range
  change IsOpen (Set.range (P.ball.map ∘
    (Subtype.val : Metric.ball (0 : StandardCapSpace) 2 → StandardCapSpace))) at h
  simpa only [Set.range_comp, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using h

noncomputable def retainedAnnularPoint : eventCapComplementOpen F T hT :=
  ⟨P.ball.map capAnnularPoint.val, P.ball_annular_mem (by rw [capAnnularPoint_norm]; norm_num)⟩

theorem retainedAnnularPoint_mem : P.retainedAnnularPoint.val ∈
    P.ball.map '' Metric.ball (0 : StandardCapSpace) 2 :=
  ⟨capAnnularPoint.val, capAnnularPoint.property, rfl⟩

theorem retained_annulus_connected : IsConnected
    {y : eventCapComplementOpen F T hT | y.val ∈ P.ball.map '' Metric.ball 0 2} := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  let : ConnectedSpace (Set.Ioo (1 : ℝ) 2) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo (by norm_num))
  have hnorm (z : UnitTwoSphere × Set.Ioo (1 : ℝ) 2) :
      ‖z.2.val • z.1.val‖ = z.2.val := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans z.2.property.1)]
    simp
  let f : UnitTwoSphere × Set.Ioo (1 : ℝ) 2 → eventCapComplementOpen F T hT :=
    fun z => ⟨P.ball.map (z.2.val • z.1.val), P.ball_annular_mem (by
      rw [hnorm]; exact z.2.property)⟩
  have hg : Continuous (fun z : UnitTwoSphere × Set.Ioo (1 : ℝ) 2 =>
      z.2.val • z.1.val) :=
    (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)
  have hf : Continuous f := (P.ball.map_smooth.continuousOn.comp_continuous hg (by
    intro z
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using z.2.property.2)).subtype_mk _
  have hrange : Set.range f =
      {y : eventCapComplementOpen F T hT | y.val ∈ P.ball.map '' Metric.ball 0 2} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.2.val • z.1.val, by
        simpa only [Metric.mem_ball, dist_zero_right, hnorm] using z.2.property.2, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      have houter : 1 < ‖x‖ := (P.ball_mem_cap_complement_iff hx).mp (hxy.symm ▸ y.property)
      refine ⟨(capUnitDirection x, ⟨‖x‖, houter, ?_⟩), ?_⟩
      · simpa only [Metric.mem_ball, dist_zero_right] using hx
      · apply Subtype.ext
        change P.ball.map (‖x‖ • (capUnitDirection x).val) = y.val
        rw [capUnitDirection_radial]
        exact hxy
  rw [← hrange]
  exact isConnected_range hf

theorem retained_annulus_component_eq (y : eventCapComplementOpen F T hT)
    (hy : y.val ∈ P.ball.map '' Metric.ball (0 : StandardCapSpace) 2) :
    ConnectedComponents.mk y = ConnectedComponents.mk P.retainedAnnularPoint :=
  ConnectedComponents.coe_eq_coe'.mpr
    (P.retained_annulus_connected.subset_connectedComponent P.retainedAnnularPoint_mem hy)

end EventCapCoordinates

end PoincareConjecture.M38
