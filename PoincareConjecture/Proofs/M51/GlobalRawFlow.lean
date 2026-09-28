import PoincareConjecture.Proofs.M51.GlobalGeometry
import PoincareConjecture.Proofs.M51.GlobalEventSlabs










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : Nat}
  (Q : CompletedStageChain S N C F0 k)
  (m13 : GeneralizedParabolicRescalingTheory.{u} 3)



noncomputable def globalFlow : SurgeryFlowData.{u} where
  standard_initial := F0.standard_initial
  local_constants := F0.local_constants
  parameters := F0.parameters
  time_domain := Ici 0
  time_domain_interval := ordConnected_Ici
  time_domain_nonnegative := fun _ ht => ht
  zero_mem := show (0 : Real) ≤ 0 from le_rfl
  slice := Q.globalSlice
  metric := Q.globalMetric
  connection := Q.globalConnection
  slices_compact := Q.global_slices_compact
  no_two_sided_projective_plane := Q.global_no_two_sided_projective_plane
  initial_nonempty := Q.global_initial_nonempty
  initial_normalized := Q.global_initial_normalized
  surgery_times := Q.globalSurgeryTimes
  surgery_times_subset := Q.globalSurgeryTimes_nonnegative
  zero_not_surgery := Q.zero_not_globalSurgeryTimes
  surgery_times_locally_finite := Q.globalSurgeryTimes_locally_finite
  regular_slabs := Q.globalSlab
  slab_transport_coherent := Q.globalSlab_coherent
  event := Q.globalEvent
  vanishing_event := Q.globalVanishingEvent m13
  event_slab_compatibility := Q.globalEvent_slab_compatibility
  vanishing_slab_compatibility := Q.globalVanishingEvent_slab_compatibility m13
  maximal_intervals := Q.global_maximal_intervals m13
  extinction_permanent := Q.global_extinction_permanent



theorem globalFlow_time_domain : (Q.globalFlow m13).time_domain = Ici 0 := rfl



theorem globalFlow_parameters : (Q.globalFlow m13).parameters = F0.parameters := rfl



theorem globalFlow_pinched : SurgeryFlowPinched (Q.globalFlow m13) := Q.global_pinched



theorem globalFlow_terminalPolicy :
    SurgeryFlowTerminalPolicyOn (Q.globalFlow m13) (Q.globalFlow m13).time_domain where
  nonempty := by
    intro T _ hT hne
    let : Nonempty (Q.globalSlice T).carrier := hne
    exact Q.globalEvent_policy T hT
  vanishing := by
    intro T _ hT he
    let : IsEmpty (Q.globalSlice T).carrier := he
    exact Q.globalVanishingEvent_policy m13 T hT

end PoincareConjecture.M51.CompletedStageChain
