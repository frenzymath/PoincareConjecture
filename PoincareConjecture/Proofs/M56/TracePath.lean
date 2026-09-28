import PoincareConjecture.Proofs.M56.TraceComponents
import PoincareConjecture.Proofs.M56.SurvivorSelection
import PoincareConjecture.Proofs.M54.BasepointTransport

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

noncomputable def m56TracePath (G54 : RepairedGroupEffectsTheory.{u})
    {F : SurgeryFlowData.{u}} (W : RepairedEventChildWitness F)
    {T : ℝ} (P : M56ComponentTrace F T) (hT : T ∈ F.time_domain)
    (C0 : SurgerySelectedComponent (F.slice 0)) (hC0 : range C0.inclusion = univ)
    (hconn : IsConnected (univ : Set (F.slice 0).carrier))
    (hgroups : ∀ t ∈ F.time_domain, M56PointGroups (F.slice t)) :
    RepairedComponentPath F T W := by
  classical
  let C := m56TraceComponents P C0
  have hC := m56TraceComponents_range P C0 hC0 hconn
  choose regular hregular using m56Trace_regularDiffeomorph P C hC
  let index := fun s hs hpost =>
    m56SurvivorSelection (W.topology s.1 hs hpost) (P.point s)
  have groups (s : Icc (0 : ℝ) T) : Subsingleton (selectedFundamentalGroup (C s)) :=
    m56SelectedComponent_pointGroups (C s) (hgroups s.1 (P.time_subset s.2)) (C s).basepoint
  have finite : (F.surgery_times ∩ Icc 0 T).Finite :=
    F.surgery_times_finite_on_compact isCompact_Icc P.time_subset
  let input : RepairedGroupPersistenceInput F T C := {
    terminal_mem := hT
    time_nonnegative := F.time_domain_nonnegative hT
    time_subset := P.time_subset
    surgery_times := finite.toFinset
    surgery_times_eq := finite.coe_toFinset
    initial_group := groups ⟨0, le_rfl, F.time_domain_nonnegative hT⟩
    regular_group_equivalence := fun a b _ _ => by
      let : Unique (selectedFundamentalGroup (C a)) := @uniqueOfSubsingleton _ (groups a) 1
      let : Unique (selectedFundamentalGroup (C b)) := @uniqueOfSubsingleton _ (groups b) 1
      exact ⟨MulEquiv.ofUnique⟩
    event_factor := fun s _ _ => by
      let : Subsingleton (selectedFundamentalGroup (C s)) := groups s
      exact ⟨RepairedGroupFactorData.ofRetraction 1 1 (by
        ext x
        exact Subsingleton.elim _ _)⟩ }
  refine {
    terminal_mem := hT
    component := C
    time_subset := P.time_subset
    surgery_times := finite.toFinset
    surgery_times_eq := finite.coe_toFinset
    regular_transport := regular
    regular_transport_ambient := hregular
    event_survivor_index := fun s hs hpost => (index s hs hpost).1
    event_survivor_index_kind := fun s hs hpost => (index s hs hpost).2.1
    event_survivor := ?_
    event_time_mem := ?_
    survivor_piece_equivalence := ?_
    surgery_transition_inherited := ?_
    group_persistence_input := input
    group_persistence := G54.persistence F T C input }
  · intro s hs hpost
    exact ⟨(hC s).trans (index s hs hpost).2.2.symm,
      (W.children s.1 hs hpost).survivor_component_point_spec _ _⟩
  · intro s hs hpost
    let := hpost
    exact P.time_subset ⟨(F.event s.1 hs).tMinus_nonnegative,
      (F.event s.1 hs).tMinus_lt.le.trans s.2.2⟩
  · intro s hs hpost
    exact m56RegionComponentDiffeomorph_exists
      ((W.topology s.1 hs hpost).survivor (index s hs hpost).1 (index s hs hpost).2.1)
      (C s) ((hC s).trans (index s hs hpost).2.2.symm)
  · intro s hs hpost
    let := hpost
    obtain ⟨x, hx, hxi, hxr⟩ := P.inherited s hs hpost
    let a : Icc (0 : ℝ) T := ⟨(F.event s.1 hs).tMinus,
      (F.event s.1 hs).tMinus_nonnegative, (F.event s.1 hs).tMinus_lt.le.trans s.2.2⟩
    have hxC : x ∈ range (C a).inclusion := (hC a).symm ▸ hx
    obtain ⟨z, rfl⟩ := hxC
    exact ⟨z, hxi, (hC s).symm ▸ hxr⟩

end PoincareConjecture
