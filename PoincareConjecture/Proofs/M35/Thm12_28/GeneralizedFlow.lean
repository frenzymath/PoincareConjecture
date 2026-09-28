import PoincareConjecture.Proofs.M35.Thm12_28.Spacetime

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

def capCarrier : GeneralizedSliceCarrier where
  carrier := StandardCapSpace
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

noncomputable def box {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) :
    GeneralizedRicciFlowBox (slice J) (metric F) J where
  carrier := capCarrier
  interval := J
  relatively_open := ⟨univ, isOpen_univ, (inter_univ J).symm⟩
  flow := F
  forward _ ht := (sliceDiffeomorph ht).symm
  inverse _ ht := sliceDiffeomorph ht
  forward_openEmbedding _ ht := (sliceDiffeomorph ht).symm.toHomeomorph.isOpenEmbedding
  forward_smooth _ ht := (sliceDiffeomorph ht).symm.contMDiff
  inverse_smooth _ ht := (sliceDiffeomorph ht).contMDiff.contMDiffOn
  left_inverse _ ht := (sliceDiffeomorph ht).apply_symm_apply
  right_inverse _ ht _ _ := (sliceDiffeomorph ht).symm_apply_apply _
  metric_pullback _ ht := metric_pullback F ht

noncomputable def generalizedFlow {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) :
    GeneralizedRicciFlowData where
  slice := slice J
  interval := J
  interval_connected := F.interval
  interval_nontrivial := F.nontrivial
  slice_nonempty_iff := slice_nonempty_iff J
  metric := metric F
  connection := connection F
  space_topology := spacetimeTopology J
  space_t2 := by
    let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
    exact (spacetimeHomeomorph J).isEmbedding.t2Space
  space_secondCountable := by
    let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
    exact (spacetimeHomeomorph J).isEmbedding.secondCountableTopology
  time_continuous := time_continuous J
  slice_embedding := slice_embedding J
  box_index := Unit
  box _ := box F
  box_openEmbedding _ := by
    let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
    exact (spacetimeHomeomorph J).symm.isOpenEmbedding
  box_covers _ x := ⟨(), x.property, x.val, rfl⟩
  vertical_compatibility _ _ t _ _ _ _ h _ _ _ := by
    have hxy := congrArg (fun z : (slice J t).carrier => z.val) h
    exact Subtype.ext hxy

theorem generalizedFlow_interval {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) :
    (generalizedFlow F).interval = J := rfl

theorem generalizedFlow_box_flow {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) :
    ((generalizedFlow F).box ()).flow = F := rfl

end PoincareConjecture.M35.OrdinaryRealization
