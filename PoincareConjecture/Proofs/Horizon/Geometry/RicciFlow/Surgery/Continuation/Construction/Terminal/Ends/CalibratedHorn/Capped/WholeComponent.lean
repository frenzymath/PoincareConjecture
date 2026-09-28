import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.CompactPrefix
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.CapNoncontainment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.ClosedEnd
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeEnds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CapDirection


noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



theorem exists_compact_prefix_frontier_subset (C : CapCertificate g)
    {U : Set M} (htail : ∃ s ∈ Ioo 0 C.epsilon⁻¹,
      C.end_neck.region s C.epsilon⁻¹ ⊆ U) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ C.carrier ∧
      frontier K ⊆ U ∧ C.carrier \ K ⊆ U := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨L, hL, hcore, hLC⟩ := exists_compact_between C.closed_core_compact
    C.carrier_open C.closed_core_subset_carrier
  obtain ⟨s, hs, htail⟩ := htail
  obtain ⟨b, hsb, hb⟩ := exists_between hs.2
  let K := L ∪ (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) b))
  have hK : IsCompact K := hL.union (C.isCompact_truncated_core hb).1
  have hKC : K ⊆ C.carrier := union_subset hLC (C.isCompact_truncated_core hb).2
  have hregion : C.end_neck.region (-C.epsilon⁻¹) b ⊆ interior K :=
    (C.end_neck.isOpen_region _ _).subset_interior_iff.mpr
      (fun _ hx => Or.inr (Or.inr (subset_closure hx)))
  have hsmall {x : M} (hx : x ∈ C.carrier) (hxi : x ∉ interior K) : x ∈ U := by
    have hend : x ∈ C.end_neck.carrier :=
      (C.carrier_eq_closed_core_union_end ▸ hx).resolve_left
        (fun hc => hxi (interior_mono subset_union_left (hcore hc)))
    have hcoord := (C.end_neck.coordinate_inverse_mem x hend).2
    rw [C.end_neck_epsilon] at hcoord
    have hlo : b ≤ (C.end_neck.coordinate_inverse x).2 := le_of_not_gt
      (fun h => hxi (hregion ⟨hend, hcoord.1, h⟩))
    exact htail ⟨hend, hsb.trans_le hlo, hcoord.2⟩
  exact ⟨K, hK, hKC,
    fun x hx => hsmall (hKC (hK.isClosed.frontier_subset hx)) hx.2,
    fun x hx => hsmall hx.1 (fun hi => hx.2 (interior_subset hi))⟩



theorem exists_compact_tube_tail (C : CapCertificate g)
    {X : Set M} (tube : EpsilonTubeCertificate g X)
    (hC : C.epsilon ≤ 1 / 200) (htube : tube.epsilon ≤ 1 / 200)
    (htail : ∃ s ∈ Ioo 0 C.epsilon⁻¹,
      C.end_neck.region s C.epsilon⁻¹ ⊆ tube.carrier) :
    ∃ (K : Set M) (side : Bool) (a : ℝ),
      IsCompact K ∧ K ⊆ C.carrier ∧ a ∈ Ioo (0 : ℝ) 1 ∧
        tube.cylinder.tail side a ⊆ K ∧ C.carrier \ K ⊆ tube.carrier := by
  obtain ⟨K, hK, hKC, hfront, hrest⟩ := C.exists_compact_prefix_frontier_subset htail
  obtain ⟨a, ha, hneg, hpos, hslab, hmiddle⟩ :=
    tube.cylinder.exists_tails_disjoint_of_isCompact
      (hK.of_isClosed_subset isClosed_frontier hK.isClosed.frontier_subset) hfront
  have ha01 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, ha.2.trans (by norm_num)⟩
  have hb01 : 1 - a ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [ha.1, ha.2]
  have hside {V : Set M} (hV : IsPreconnected V) (havoid : Disjoint V (frontier K)) :
      V ⊆ interior K ∨ V ⊆ Kᶜ := by
    apply hV.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset)
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ((mem_interior_iff_notMem_frontier hxK).mpr
        (fun hf => disjoint_left.mp havoid hx hf))
    · exact Or.inr hxK
  rcases hside (tube.cylinder.isConnected_tail false ha01).isPreconnected hneg with hn | hn
  · exact ⟨K, false, a, hK, hKC, ha01, hn.trans interior_subset, hrest⟩
  rcases hside (tube.cylinder.isConnected_tail true hb01).isPreconnected hpos with hp | hp
  · exact ⟨K, true, 1 - a, hK, hKC, hb01, hp.trans interior_subset, hrest⟩
  have htrap : tube.carrier ∩ K ⊆
      tube.cylinder.coordinate '' (univ ×ˢ Icc a (1 - a)) := by
    intro x hx
    exact hmiddle ⟨hx.1, fun h => h.elim (fun h => hn h hx.2) (fun h => hp h hx.2)⟩
  have hclosure : closure (tube.carrier ∩ K) ⊆ tube.carrier :=
    (closure_minimal htrap hslab.isClosed).trans
      (tube.cylinder.coordinate_slab_subset ha.1 hb01.2)
  have havoid : Disjoint C.carrier (frontier tube.carrier) := by
    refine disjoint_left.mpr ?_
    intro x hxC hxF
    have hxnot : x ∉ tube.carrier := (tube.carrier_open.frontier_eq ▸ hxF).2
    have hxK : x ∈ K := by
      by_contra hnK
      exact hxnot (hrest ⟨hxC, hnK⟩)
    have hxi : x ∈ interior K := (mem_interior_iff_notMem_frontier hxK).mpr
      (fun h => hxnot (hfront h))
    apply hxnot
    apply hclosure
    apply mem_closure_iff.mpr
    intro V hV hxV
    obtain ⟨y, hy, hytube⟩ := mem_closure_iff.mp (frontier_subset_closure hxF)
      (V ∩ interior K) (hV.inter isOpen_interior) ⟨hxV, hxi⟩
    exact ⟨y, hy.1, hytube, interior_subset hy.2⟩
  have hmeet : (C.carrier ∩ interior tube.carrier).Nonempty := by
    obtain ⟨s, hs, hst⟩ := htail
    obtain ⟨x, hx⟩ := (C.end_neck.isConnected_region
      (by rw [C.end_neck_epsilon]; linarith [hs.1, inv_pos.mpr C.epsilon_pos])
      (by rw [C.end_neck_epsilon]) hs.2).nonempty
    exact ⟨x, C.end_neck_subset hx.1, tube.carrier_open.interior_eq.symm ▸ hst hx⟩
  exact False.elim (C.tube_noncontainment_of_epsilon_le tube hC htube
    ((Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      C.isConnected_carrier.isPreconnected havoid hmeet).trans interior_subset))

end PoincareConjecture.CapCertificate

namespace PoincareConjecture.TerminalEnd

universe u

variable {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension G T} {K : TerminalComponentPath E}



theorem exists_compact_cappedTube_attachment (e : TerminalEnd K)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (Y : CappedTubeCertificate (E.extended.metric T))
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ Y.carrier) :
    ∃ (L : Set (E.extended.slice T).carrier) (a : ℝ),
      IsCompact L ∧ L ⊆ Y.cap.carrier ∧ a ∈ Ioo (0 : ℝ) 1 ∧
      Y.tube.cylinder.tail Y.attachment_side a ⊆ L ∧
      Y.cap.carrier \ L ⊆ Y.tube.carrier := by
  obtain ⟨L, side, a, hL, hLC, ha, hsub, hrest⟩ :=
    Y.cap.exists_compact_tube_tail Y.tube Y.cap.epsilon_le_threshold
      Y.tube.epsilon_le_threshold Y.attachment.cap_tail
  have heq : side = Y.attachment_side := by
    by_contra hn
    have hside : side = !Y.attachment_side := by
      cases side <;> cases h : Y.attachment_side <;> simp_all
    obtain ⟨k, _, hk⟩ := e.exists_cappedTube_direction hproper Y n htail a ha
    exact e.tail_image_not_subset_compact k hL
      ((hk k le_rfl).trans (hside ▸ hsub))
  exact ⟨L, a, hL, hLC, ha, heq ▸ hsub, hrest⟩




theorem cappedTube_carrier_eq_component (e : TerminalEnd K)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (Y : CappedTubeCertificate (E.extended.metric T))
    {X : Set (E.extended.slice T).carrier} (hX : IsClosed X)
    (hfront : IsCompact (frontier X)) (hXY : X ⊆ Y.carrier)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X) :
    Y.carrier = K.component := by
  let Z := X \ Y.cap.carrier
  have hZclosed : IsClosed Z := hX.inter Y.cap.carrier_open.isClosed_compl
  have hZtube : Z ⊆ Y.tube.carrier := by
    intro x hx
    exact (Y.carrier_eq_union ▸ hXY hx.1).resolve_left hx.2
  have hcap : IsCompact (closure Y.cap.carrier) :=
    Y.cap.isCompact_closure_of_scalar_proper (E.extended.connection T) hproper
  have hZfront : IsCompact (frontier Z) := by
    apply (hfront.union hcap).of_isClosed_subset isClosed_frontier
    intro x hx
    rcases frontier_inter_subset X Y.cap.carrierᶜ hx with hx | hx
    · exact Or.inl hx.1
    · exact Or.inr (frontier_subset_closure (by simpa only [frontier_compl] using hx.2))
  obtain ⟨m, hm⟩ := e.exists_tail_disjoint_cap hproper Y.cap
  have htailZ : Subtype.val '' e.tail (max n m) ⊆ Z := by
    intro x hx
    exact ⟨htail (image_mono (e.nested (le_max_left _ _)) hx),
      fun hc => disjoint_left.mp (hm (max n m) (le_max_right _ _)) hx hc⟩
  let tube : EpsilonTubeCertificate (E.extended.metric T) Z :=
    { Y.tube with contains_X := hZtube }
  obtain ⟨side, a, k, ha, _, _, hclosed, _, hcarry⟩ :=
    e.exists_proper_closed_tube_tail hZclosed hZfront tube (max n m) htailZ
  have hside : side = !Y.attachment_side := by
    by_contra hn
    have heq : side = Y.attachment_side := by
      cases side <;> cases h : Y.attachment_side <;> simp_all
    obtain ⟨l, _, hl⟩ := e.exists_cappedTube_direction hproper Y n (htail.trans hXY) a ha
    obtain ⟨x, hx⟩ := (e.tail_image_connected (max k l)).nonempty
    have hleft := (Y.tube.cylinder.mem_tail_iff Y.attachment_side ha).mp
      (show x ∈ Y.tube.cylinder.tail Y.attachment_side a from
        heq ▸ hcarry (max k l) (le_max_left _ _) hx)
    have hright := (Y.tube.cylinder.mem_tail_iff (!Y.attachment_side) ha).mp
      (hl (max k l) (le_max_right _ _) hx)
    cases h : Y.attachment_side <;> simp only [h, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] at hleft hright <;> linarith [hleft.2, hright.2]
  obtain ⟨L, b, hL, hLC, hb, hattach, hrest⟩ :=
    e.exists_compact_cappedTube_attachment hproper Y n (htail.trans hXY)
  have hclosed' : IsClosed (Y.tube.cylinder.closedTail (!Y.attachment_side) b) :=
    Y.tube.cylinder.isClosed_closedTail_of_isClosed_closedTail (!Y.attachment_side) ha hb
      (by simpa only [tube, hside] using hclosed)
  have htube : Y.tube.carrier ⊆ L ∪ Y.tube.cylinder.closedTail (!Y.attachment_side) b := by
    intro x hx
    by_cases ha' : x ∈ Y.tube.cylinder.tail Y.attachment_side b
    · exact Or.inl (hattach ha')
    · right
      apply (Y.tube.cylinder.mem_closedTail_iff (!Y.attachment_side) hb).mpr
      refine ⟨hx, ?_⟩
      have hn : ¬ (if Y.attachment_side then b < (Y.tube.cylinder.inverse x).2
          else (Y.tube.cylinder.inverse x).2 < b) :=
        fun h => ha' ((Y.tube.cylinder.mem_tail_iff Y.attachment_side hb).mpr ⟨hx, h⟩)
      cases h : Y.attachment_side <;> simp only [h, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, if_false, if_true, not_lt] at hn ⊢ <;> exact hn
  have hYeq : Y.carrier = L ∪ Y.tube.cylinder.closedTail (!Y.attachment_side) b := by
    apply Subset.antisymm
    · intro x hx
      rcases Y.carrier_eq_union ▸ hx with hc | ht
      · by_cases hxL : x ∈ L
        · exact Or.inl hxL
        · exact htube (hrest ⟨hc, hxL⟩)
      · exact htube ht
    · exact union_subset (hLC.trans Y.cap_subset)
        (fun _ hx => Y.tube_subset ((Y.tube.cylinder.mem_closedTail_iff
          (!Y.attachment_side) hb).mp hx).1)
  have hYclosed : IsClosed Y.carrier := hYeq ▸ hL.isClosed.union hclosed'
  have hYopen : IsOpen Y.carrier := Y.carrier_eq_union ▸
    Y.cap.carrier_open.union Y.tube.carrier_open
  obtain ⟨x, hx⟩ := (e.tail_image_connected n).nonempty
  have hxY := hXY (htail hx)
  have hxK : x ∈ K.component := by
    obtain ⟨z, _, rfl⟩ := hx
    exact z.property
  have hcomponent : Y.carrier = connectedComponent x := by
    apply Subset.antisymm (Y.connected.isPreconnected.subset_connectedComponent hxY)
    have havoid : Disjoint (connectedComponent x) (frontier Y.carrier) := by
      rw [(show IsClopen Y.carrier from ⟨hYclosed, hYopen⟩).frontier_eq]
      exact disjoint_empty _
    exact (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      isPreconnected_connectedComponent havoid
      ⟨x, mem_connectedComponent, hYopen.interior_eq.symm ▸ hxY⟩).trans interior_subset
  exact hcomponent.trans ((connectedComponent_eq (K.component_eq ▸ hxK)).symm.trans
    K.component_eq.symm)

end PoincareConjecture.TerminalEnd
