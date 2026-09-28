import PoincareConjecture.Proofs.M38.CapIncidentAssembly
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.NeckCap.Cap.Closing.Tube.CapAbsorption











set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38



theorem exists_capped_tube_region_comparison_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 1000 ∧
      ∀ (A : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 A.carrier)
        (C : CappedTubeCertificate g), C.cap.epsilon ≤ epsilon0 →
        Nonempty (SurgeryRegionEquivalence A A C.carrier C.cap.carrier) := by
  obtain ⟨epsilon0, hpos, hsmall, habsorb⟩ :=
    M38Schoenflies.PoincareConjecture.CapTubeAttachment.exists_absorption_threshold.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro A g C hepsilon
  obtain ⟨_, _, D, _, _⟩ := habsorb C.attachment hepsilon
  let U : TopologicalSpace.Opens A.carrier := ⟨C.cap.carrier, C.cap.carrier_open⟩
  let V : TopologicalSpace.Opens A.carrier := ⟨C.tube.carrier, C.tube.carrier_open⟩
  let p : U := ⟨C.cap.end_neck.center,
    C.cap.end_neck_subset
      (C.cap.end_neck.central_sphere_subset C.cap.end_neck.center_on_central_sphere)⟩
  have E : SurgeryRegionEquivalence A A (C.cap.carrier ∪ C.tube.carrier) C.cap.carrier :=
    openDiffeomorphRegions (U ⊔ V) U D.symm (D p)
  rw [← C.carrier_eq_union] at E
  exact ⟨E⟩




theorem exists_capped_tube_incident_assembly_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 1000 ∧
      ∀ (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
        [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
        (x : eventDiscardedOpen F T hT) (t : Ico (F.event T hT).tMinus T)
        (C : CappedTubeCertificate (F.metric t.val)), C.cap.epsilon ≤ epsilon0 →
        (F.event T hT).pre_identify t ''
          closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ C.carrier →
        let A := componentCarrier (cappedDiscardedCarrier F T hT P)
          (cappedOldInclusion F T hT P x)
        Nonempty (SurgeryPositiveSpaceform A) ∧
          Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  obtain ⟨epsilon0, hpos, hsmall, hcompare⟩ :=
    exists_capped_tube_region_comparison_threshold.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro F T hT _ P x t C hepsilon hsource
  obtain ⟨E⟩ := hcompare (F.slice t.val) (F.metric t.val) C hepsilon
  have hC : IsOpen C.carrier := by
    rw [C.carrier_eq_union]
    exact C.cap.carrier_open.union C.tube.carrier_open
  exact spaceform_incident_assembly_of_cap_comparison F T hT P x t C.cap hC E hsource

end PoincareConjecture.M38
