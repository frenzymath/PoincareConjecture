import PoincareLib.Topology.Manifold.Surgery.Event.Cap.CapCollarSides

/-!
# Closed attachment graphs for the discarded-side cap patches

The open unit-to-double annulus attaches to the positive collar. Its graph
remains closed in the product of the open ball patch and the discarded
interior: the only inner boundary limit lands on the excluded central sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

/-- The annular coordinates used to attach a discarded-side cap. -/
noncomputable def capAttachCoordinates (x : StandardCapSpace) : RoundCylinderSpace :=
  (capUnitDirection x, ‖x‖ - 1)

/-- The annular coordinates are smooth away from the origin. -/
theorem capAttachCoordinates_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ capAttachCoordinates
      ({0}ᶜ : Set StandardCapSpace) := by
  apply capUnitDirection_smooth.prodMk
  intro x hx
  have hn : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖) x := contDiffAt_norm ℝ hx
  exact (hn.sub contDiffAt_const).contMDiffAt.contMDiffWithinAt

/-- The attachment graph is closed even though its annular source is
open, because its radius-one limit is absent from the discarded interior. -/
theorem cap_attachment_graph_closed {A : Type u} [TopologicalSpace A] [T2Space A]
    (C : RoundCylinderSpace → A)
    (hC : ContinuousOn C (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
    {S : Set A} (hcentral : ∀ z : UnitTwoSphere, C (z, 0) ∈ S) :
    IsClosed {q : Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ) |
      1 < ‖q.1.val‖ ∧ C (capAttachCoordinates q.1.val) = q.2.val} := by
  let V : Set (Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ)) :=
    {q | 1 ≤ ‖q.1.val‖}
  have hv : Continuous (fun q : Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ) => q.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hV : IsClosed V := isClosed_le continuous_const (continuous_norm.comp hv)
  have hnzero : Set.MapsTo (fun q : Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ) => q.1.val)
      V ({0}ᶜ : Set StandardCapSpace) := by
    intro q hq
    change q.1.val ≠ 0
    apply norm_pos_iff.mp
    exact zero_lt_one.trans_le hq
  have hcoord : ContinuousOn
      (fun q : Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ) => capAttachCoordinates q.1.val) V :=
    capAttachCoordinates_smooth.continuousOn.comp hv.continuousOn hnzero
  have hdomain : Set.MapsTo
      (fun q : Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ) => capAttachCoordinates q.1.val)
      V (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
    intro q hq
    have hupper : ‖q.1.val‖ < 2 := by
      simpa only [Metric.mem_ball, dist_zero_right] using q.1.property
    refine ⟨Set.mem_univ _, ?_, ?_⟩ <;> change _ < _ <;> dsimp [capAttachCoordinates]
    · linarith [show 1 ≤ ‖q.1.val‖ from hq]
    · linarith
  have hclosed : IsClosed {q : Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ) |
      q ∈ V ∧ C (capAttachCoordinates q.1.val) = q.2.val} :=
    hV.isClosed_eq (hC.comp hcoord hdomain)
      (continuous_subtype_val.comp continuous_snd).continuousOn
  have heq : {q : Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ) |
      q ∈ V ∧ C (capAttachCoordinates q.1.val) = q.2.val} =
      {q : Metric.ball (0 : StandardCapSpace) 2 × ↥(Sᶜ) |
        1 < ‖q.1.val‖ ∧ C (capAttachCoordinates q.1.val) = q.2.val} := by
    ext q
    constructor
    · rintro ⟨hq, heq⟩
      refine ⟨lt_of_le_of_ne hq ?_, heq⟩
      intro hnorm
      have hzero : capAttachCoordinates q.1.val = (capUnitDirection q.1.val, 0) := by
        simp [capAttachCoordinates, ← hnorm]
      rw [hzero] at heq
      exact q.2.property (heq ▸ hcentral (capUnitDirection q.1.val))
    · exact fun h => ⟨h.1.le, h.2⟩
  rwa [← heq]

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)

/-- The event's actual cap-coordinate zero section is contained in the
closed retained region and hence excluded from the discarded interior. -/
theorem event_cap_collar_central_retained {r : ℝ} (hr : 0 < r) (c : ℝ)
    (hball : F.standard_initial.metric.ball 0
      (F.standard_initial.cylindrical_end.radius + 4) = Metric.ball 0 r)
    (z : UnitTwoSphere) :
    eventCapCollar F T hT i r c (z, 0) ∈ (F.event T hT).retained_pre := by
  apply (F.event T hT).retained_pre_compact.isClosed.frontier_subset
  rw [(F.event T hT).pre_boundary]
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [← event_cap_collar_central F T hT i hr c hball]
  exact Set.mem_image_of_mem _ ⟨Set.mem_univ _, Set.mem_singleton _⟩

/-- The literal annular attachment to the discarded event interior has
a closed graph, the Hausdorff condition for the subsequent cap quotient. -/
theorem event_cap_attachment_graph_closed {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    (hdom : {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} ⊆
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5) ∩
        ((F.event T hT).local_result i).cap_map ⁻¹'
          (((F.event T hT).local_result i).collapse ''
            ((F.event T hT).necks i).neck.region
              (-((F.event T hT).necks i).neck.epsilon⁻¹) 1))
    (hball : F.standard_initial.metric.ball 0
      (F.standard_initial.cylindrical_end.radius + 4) = Metric.ball 0 r) :
    IsClosed {q : Metric.ball (0 : StandardCapSpace) 2 × ↥((F.event T hT).retained_preᶜ) |
      1 < ‖q.1.val‖ ∧ eventCapCollar F T hT i r c (capAttachCoordinates q.1.val) = q.2.val} :=
  cap_attachment_graph_closed _ (event_cap_collar_smooth F T hT i hc hcr hdom).continuousOn
    (event_cap_collar_central_retained F T hT i (hc.trans hcr) c hball)

end PoincareMT.M38
