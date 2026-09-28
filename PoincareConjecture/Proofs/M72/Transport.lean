import PoincareConjecture.Definitions.M72FiniteReconstruction












set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture


noncomputable def m72RegionPostcompose {P Q R : GeneralizedSliceCarrier.{u}}
    {U : Set Q.carrier} (E : SurgeryRegionEquivalence P Q Set.univ U)
    (d : Diffeomorph (𝓡 3) (𝓡 3) Q.carrier R.carrier ∞) :
    SurgeryRegionEquivalence P R Set.univ (d '' U) where
  map := d ∘ E.map
  inverse := E.inverse ∘ d.symm
  map_image := by rw [Set.image_comp, E.map_image]
  inverse_image := by
    calc
      (E.inverse ∘ d.symm) '' (d '' U) = E.inverse '' U := by
        ext x
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, by simp⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨d y, ⟨y, hy, rfl⟩, by simp⟩
      _ = Set.univ := E.inverse_image
  left_inverse := by
    intro x hx
    simpa using E.left_inverse hx
  right_inverse := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using congrArg d (E.right_inverse hy)
  map_smooth := d.contMDiff.comp_contMDiffOn E.map_smooth
  inverse_smooth := E.inverse_smooth.comp d.symm.contMDiff.contMDiffOn (by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy)


noncomputable def M72SuccessorTransport.component_transport
    {F : SurgeryFlowData.{u}} {H T T' : ℝ}
    {hT : T ∈ F.surgery_times} {hT' : T' ∈ F.surgery_times}
    {E : M72EventTopologyData F T hT}
    {E' : M72EventTopologyData F T' hT'}
    {i : Fin E.conclusion.piece_count}
    (S : M72SuccessorTransport F H T T' hT hT' E E' i)
    (hi : E.conclusion.kind i = .survivor) :
    M72ComponentAssemblyTransport (E.conclusion.piece i) (F.slice E'.pre_time) where
  region := S.transport '' E.conclusion.survivor_region i
  component_equivalence := m72RegionPostcompose (E.conclusion.survivor i hi) S.transport

theorem M72SuccessorTransport.component_region_eq
    {F : SurgeryFlowData.{u}} {H T T' : ℝ}
    {hT : T ∈ F.surgery_times} {hT' : T' ∈ F.surgery_times}
    {E : M72EventTopologyData F T hT}
    {E' : M72EventTopologyData F T' hT'}
    {i : Fin E.conclusion.piece_count}
    (S : M72SuccessorTransport F H T T' hT hT' E E' i)
    (hi : E.conclusion.kind i = .survivor) :
    (S.component_transport hi).region = connectedComponent S.component_point :=
  S.survivor_image

theorem M72SuccessorTransport.component_map_eq
    {F : SurgeryFlowData.{u}} {H T T' : ℝ}
    {hT : T ∈ F.surgery_times} {hT' : T' ∈ F.surgery_times}
    {E : M72EventTopologyData F T hT}
    {E' : M72EventTopologyData F T' hT'}
    {i : Fin E.conclusion.piece_count}
    (S : M72SuccessorTransport F H T T' hT hT' E E' i)
    (hi : E.conclusion.kind i = .survivor) (x : (E.conclusion.piece i).carrier) :
    (S.component_transport hi).component_equivalence.map x =
      S.transport ((E.conclusion.survivor i hi).map x) := rfl

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}


noncomputable def m72ReconstructionLedger (I : M72ReconstructionInput N) :
    M72ReconstructionLedger I where
  event_times := (I.global.certificate.local_finite
    (Set.Icc 0 I.extinction.extinction_time) isCompact_Icc).toFinset
  event_times_eq := Set.Finite.coe_toFinset _


theorem m72SuccessorTargetInLedger (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L)
    (i : Fin (M72EventTopology I L e).conclusion.piece_count)
    (S : M72SuccessorChoice I.global.certificate.flow I.extinction.extinction_time
      I.local_topology.event e.1 (M72EventFlowMem I L e) (M72EventTopology I L e) i) :
    ∃ e' : M72EventIndex I L,
      S.target_time = e'.1 ∧ HEq S.target_event (M72EventTopology I L e') := by
  have hnonneg : 0 ≤ S.target_time :=
    I.global.certificate.flow.time_domain_nonnegative
      (I.global.certificate.flow.surgery_times_subset S.target_mem)
  have hmem : S.target_time ∈ (↑L.event_times : Set ℝ) := by
    rw [L.event_times_eq]
    exact ⟨S.target_mem, hnonneg, S.target_before⟩
  exact ⟨⟨S.target_time, hmem⟩, rfl, HEq.rfl⟩

end PoincareConjecture
