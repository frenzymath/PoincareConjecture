import PoincareLib.Topology.Manifold.Surgery.Event.Cap.CapBallEmbedding
import PoincareLib.Topology.Manifold.Surgery.Event.Local.LocalCapCollar
import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventCollars

/-!
# The actual cap ball and its pre-surgery collar

One collar width is chosen for both the ball parametrization and the
inverse-collapse collar. The negative gluing equation is the event's
unconditional local retention equation in these coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

/-- A single positive width works both outside the closed ball and on the
whole boundary shell inside the extended collapse collar. -/
theorem exists_local_cap_collar_width
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {I : MetricSurgeryInput K g} (R : MetricSurgeryResult g₀ I)
    {r : ℝ} (hr : 0 < r)
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r) :
    ∃ c : ℝ, 0 < c ∧ c < r ∧
      Metric.ball 0 (r + c) ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) ∧
      {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} ⊆
        g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) ∩
          R.cap_map ⁻¹' (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1) := by
  have hclosed := standard_cap_ball_extended g₀ hr hball
  obtain ⟨b, hb, hbr, hbdom⟩ := exists_cap_ball_width hr (standard_ball_open _ _) hclosed
  obtain ⟨d, hd, _, hddom⟩ := exists_cap_sphere_shell hr
    (local_cap_boundary_neighborhood R hr hball hclosed).1
    (local_cap_boundary_neighborhood R hr hball hclosed).2
  obtain ⟨c, hc, hcm⟩ := exists_between (lt_min hb hd)
  have hcb : c ≤ b := (hcm.trans_le (min_le_left b d)).le
  have hcd : c ≤ d := (hcm.trans_le (min_le_right b d)).le
  refine ⟨c, hc, hcb.trans_lt hbr,
    (Metric.ball_subset_ball (by linarith : r + c ≤ r + b)).trans hbdom, ?_⟩
  intro x hx
  exact hddom ⟨by linarith [hx.1], by linarith [hx.2]⟩

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)

/-- The cap-coordinate collar in the literal pre-surgery slice. -/
noncomputable def eventCapCollar (r c : ℝ) :
    RoundCylinderSpace → (F.slice (F.event T hT).tMinus).carrier :=
  (F.event T hT).limit_identify.inverse ∘ localCapCollar ((F.event T hT).local_result i) r c

/-- Its total inverse retains the actual limit identification. -/
noncomputable def eventCapCollarInverse (r c : ℝ) :
    (F.slice (F.event T hT).tMinus).carrier → RoundCylinderSpace :=
  localCapCollarInverse ((F.event T hT).local_result i) r c ∘
    (F.event T hT).limit_identify.map

variable {r c : ℝ} (hc : 0 < c) (hcr : c < r)
  (hdom : {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} ⊆
    F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5) ∩
      ((F.event T hT).local_result i).cap_map ⁻¹'
        (((F.event T hT).local_result i).collapse ''
          ((F.event T hT).necks i).neck.region (-((F.event T hT).necks i).neck.epsilon⁻¹) 1))

include hc hcr hdom

/-- The pre-surgery collar is smooth on the full open cylinder. -/
theorem event_cap_collar_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (eventCapCollar F T hT i r c)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
  (contMDiffOn_univ.mp (F.event T hT).limit_identify.inverse_smooth).comp_contMDiffOn
    (local_cap_collar_smooth _ hc hcr hdom)

/-- The displayed inverse recovers both coordinates on the true domain. -/
theorem event_cap_collar_left_inverse :
    Set.LeftInvOn (eventCapCollarInverse F T hT i r c) (eventCapCollar F T hT i r c)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  intro z hz
  change localCapCollarInverse _ r c ((F.event T hT).limit_identify.map
    ((F.event T hT).limit_identify.inverse (localCapCollar _ r c z))) = z
  rw [(F.event T hT).limit_identify.right_inverse (Set.mem_univ _)]
  exact local_cap_collar_left_inverse _ hc hcr hdom hz

/-- The forward map likewise recovers each point of its actual image. -/
theorem event_cap_collar_right_inverse :
    Set.LeftInvOn (eventCapCollar F T hT i r c) (eventCapCollarInverse F T hT i r c)
      (eventCapCollar F T hT i r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rintro x ⟨z, hz, rfl⟩
  exact congrArg (eventCapCollar F T hT i r c)
    (event_cap_collar_left_inverse F T hT i hc hcr hdom hz)

/-- Inverse smoothness is restricted to the actual image in the pre-slice. -/
theorem event_cap_collar_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (eventCapCollarInverse F T hT i r c)
      (eventCapCollar F T hT i r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  have hregular : eventCapCollar F T hT i r c ''
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) ⊆ (F.event T hT).regular_limit := by
    rintro x ⟨z, _, rfl⟩
    exact limit_inverse_mem F T hT _
  apply (local_cap_collar_inverse_smooth _ hc hcr hdom).comp
    ((F.event T hT).limit_identify.map_smooth.mono hregular)
  rintro x ⟨z, hz, rfl⟩
  exact ⟨z, hz, ((F.event T hT).limit_identify.right_inverse (Set.mem_univ _)).symm⟩

/-- The cap-coordinate collar is an open neighborhood in the actual pre-slice. -/
theorem event_cap_collar_open :
    IsOpen (eventCapCollar F T hT i r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  change IsOpen (((F.event T hT).limit_identify.inverse ∘
    localCapCollar _ r c) '' _)
  rw [Set.image_comp]
  exact (limit_inverse_openEmbedding F T hT).isOpenMap _
    (local_cap_collar_open _ hc hcr hdom)

/-- Negative shell points pull back to the actual retained pre-region. -/
theorem event_cap_collar_negative_retained {z : UnitTwoSphere} {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0)
    (hball : F.standard_initial.metric.ball 0
      (F.standard_initial.cylindrical_end.radius + 4) = Metric.ball 0 r) :
    eventCapCollar F T hT i r c (z, s) ∈ (F.event T hT).retained_pre := by
  have hneg := local_cap_collar_negative ((F.event T hT).local_result i) hc hcr hdom
    (z := z) hs
    hball (standard_cap_ball_extended _ (hc.trans hcr) hball)
  obtain ⟨x, hx, heq⟩ := (F.event T hT).neck_negative_retained i hneg
  change (F.event T hT).limit_identify.inverse (localCapCollar _ r c (z, s)) ∈ _
  rw [← heq, (F.event T hT).limit_identify.left_inverse
    ((F.event T hT).retained_pre_subset hx)]
  exact hx

/-- The exact negative gluing identity uses the same radial adjustment as
the actual cap ball, including its outer collar. -/
theorem event_cap_collar_negative_gluing
    (hball : F.standard_initial.metric.ball 0
      (F.standard_initial.cylindrical_end.radius + 4) = Metric.ball 0 r)
    (hballDom : Metric.ball (0 : StandardCapSpace) (r + c) ⊆
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5))
    (z : UnitTwoSphere) (s : ℝ) (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    eventCapCollar F T hT i r c (z, s) = (F.event T hT).retention.inverse
      ((eventCapBall F T hT i r c hc hcr hballDom).map ((1 - s) • z.val)) := by
  have hz : (z, s) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Set.mem_univ _, hs.1, hs.2.trans zero_lt_one⟩
  have hneg := local_cap_collar_negative ((F.event T hT).local_result i) hc hcr hdom
    (z := z) hs
    hball (standard_cap_ball_extended _ (hc.trans hcr) hball)
  have hret := (F.event T hT).local_retention i _ hneg
  rw [local_cap_collar_collapse _ hc hcr hdom hz] at hret
  have hrad : capRadialDiffeomorph r c hc hcr ((1 - s) • z.val) =
      capShellMap r c (z, s) := by
    rw [capRadialDiffeomorph_smul hc hcr z (1 - s) (by linarith [hs.2])]
    congr 1
    dsimp [capShellMap]
    ring
  rw [eventCapBall_map, hrad, hret]
  exact ((F.event T hT).retention.left_inverse
    (event_cap_collar_negative_retained F T hT i hc hcr hdom hs hball)).symm

end PoincareMT.M38
