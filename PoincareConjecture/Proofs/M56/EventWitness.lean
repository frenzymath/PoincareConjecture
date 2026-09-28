import PoincareConjecture.Proofs.M56.GroupInduction









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



noncomputable def m56RawTopology {F : SurgeryFlowData.{u}}
    (L : RawLocalSurgeryTopologyData F) (T : ℝ) (hT : T ∈ F.surgery_times)
    (hpost : Nonempty (F.slice T).carrier) :
    letI := hpost
    SurgeryTopologyConclusion (F.slice (F.event T hT).tMinus) (F.slice T) := by
  let := hpost
  exact (Classical.choice (L.nonempty_reconstruction T hT)).conclusion



theorem m56RawPointGroups (G54 : RepairedGroupEffectsTheory.{u})
    {F : SurgeryFlowData.{u}} (L : RawLocalSurgeryTopologyData F)
    (hzero : M56PointGroups (F.slice 0))
    (T : ℝ) (hT : T ∈ F.time_domain) : M56PointGroups (F.slice T) := by
  apply m56PointGroups_induction F hzero _ T hT
  intro s hs hpost hpre
  apply m56PointGroups_of_survivors (m56RawTopology L s hs hpost)
  intro i hi x
  let E := Classical.choice (G54.effects (m56RawTopology L s hs hpost))
  let := hpre (E.parent_basepoint i hi x)
  exact (E.piece_effect i hi x).target_subsingleton



noncomputable def m56PoincareWitness (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    {F : SurgeryFlowData.{u}} (L : RawLocalSurgeryTopologyData F)
    (hzero : M56PointGroups (F.slice 0)) : RepairedEventChildWitness F := by
  let C := m56RawTopology L
  let E := fun T hT hpost => Classical.choice (G54.effects (C T hT hpost))
  have parent : ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      (hpost : Nonempty (F.slice T).carrier), letI := hpost
      ∀ i : Fin (C T hT hpost).piece_count,
        ∀ hi : (C T hT hpost).kind i = .survivor,
          ∀ x : ((C T hT hpost).piece i).carrier,
            Subsingleton (FundamentalGroup (F.slice (F.event T hT).tMinus).carrier
              ((E T hT hpost).parent_basepoint i hi x)) := by
    intro T hT hpost i hi x
    let := hpost
    exact m56RawPointGroups G54 L hzero _
      (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
        ⟨(F.event T hT).tMinus_nonnegative, (F.event T hT).tMinus_lt.le⟩) _
  exact {
    topology := C
    effects := E
    parent_groups_subsingleton := parent
    children := fun T hT hpost => Classical.choice
      (G55.components G54 (C T hT hpost) (E T hT hpost) rfl (parent T hT hpost)) }

end PoincareConjecture
