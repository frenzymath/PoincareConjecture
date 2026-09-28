import PoincareConjecture.Proofs.M38.M25Adapter
import PoincareConjecture.Proofs.M38.UnattachedAssembly
import PoincareConjecture.Proofs.M38.CappedTubeIncident
import PoincareConjecture.Proofs.M38.LateSphereBundleIncident
import PoincareConjecture.Proofs.M38.LateProjectiveIncident
import PoincareConjecture.Proofs.M38.LateSpaceformIncident

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem closed_certificate_incident_assembly
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (t : Ico (F.event T hT).tMinus T)
    {kind : ClosedComponentKind} {U : Set (F.slice t.val).carrier}
    (C : ClosedComponentCertificate kind U)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ U) :
    ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
      (∀ j, IsCompact (univ : Set (D j).carrier)) ∧
      (∀ j, IsConnected (univ : Set (D j).carrier)) ∧
      (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
        Nonempty (SurgeryPositiveSpaceform (D j))) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly D
        (componentCarrier (cappedDiscardedCarrier F T hT P)
          (cappedOldInclusion F T hT P x))) := by
  cases kind with
  | threeSphere =>
      obtain ⟨hs, ha⟩ := spherical_incident_assembly_of_closed_sphere F T hT P x t C hsource
      exact ⟨1, fun _ => _, fun _ => (Classical.choice hs).compact,
        fun _ => (Classical.choice hs).connected, fun _ => Or.inr hs, ha⟩
  | realProjectiveThree =>
      obtain ⟨hs, ha⟩ := spaceform_incident_assembly_of_closed_projective F T hT P x t C hsource
      exact ⟨1, fun _ => _, fun _ => (Classical.choice hs).compact,
        fun _ => (Classical.choice hs).connected, fun _ => Or.inr hs, ha⟩
  | realProjectiveThreeConnectedSum =>
      exact projectiveDouble_incident_assembly_of_closed_double F T hT P x t C hsource

theorem exists_positiveCap_discarded_assembly
    (N : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ min N.epsilon₀ (1 / 1000) ∧
      ∀ (F : SurgeryFlowData.{u}), SurgeryFlowAdmissible F →
        F.parameters.epsilon ≤ epsilon0 →
        ∀ (T : ℝ) (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
          (P : ∀ i, EventCapCoordinates F T hT i),
          ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
            (∀ j, IsCompact (univ : Set (D j).carrier)) ∧
            (∀ j, IsConnected (univ : Set (D j).carrier)) ∧
            (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
              Nonempty (SurgeryPositiveSpaceform (D j))) ∧
            Nonempty (SmoothFiniteConnectedSumAssembly D
              (cappedDiscardedCarrier F T hT P)) := by
  classical
  obtain ⟨eta, heta, hetasmall, habsorb⟩ :=
    exists_capped_tube_incident_assembly_threshold.{u}
  refine ⟨min N.epsilon₀ eta, lt_min N.epsilon₀_pos heta,
    le_min (min_le_left _ _) ((min_le_right _ _).trans hetasmall), ?_⟩
  intro F hF hepsilon T hT _ P
  have hN : F.parameters.epsilon ≤ N.epsilon₀ := hepsilon.trans (min_le_left _ _)
  obtain ⟨t, _, _, x, region, hrep, hregion, _, _, _, hmodel⟩ :=
    exists_capped_canonical_regions F T hT P N hF hN
  apply exists_classifiedAssembly_of_components (cappedDiscardedCarrier F T hT P)
    (cappedDiscardedCarrier_compact F T hT P)
  intro q
  let c := ConnectedComponents.mk q
  have hcarrier : componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P (x c)) =
      componentCarrier (cappedDiscardedCarrier F T hT P) q := by
    apply congrArg (openCarrier (cappedDiscardedCarrier F T hT P))
    apply TopologicalSpace.Opens.ext
    exact ConnectedComponents.coe_eq_coe.mp (hrep c)
  rw [← hcarrier]
  by_cases hu : ∀ i, ConnectedComponents.mk (P i).attachmentPoint ≠ ConnectedComponents.mk (x c)
  · exact exists_unattached_component_assemblies F T hT P N hF hN (x c) hu
  · rcases hmodel c with hA | hC | hR
    · obtain ⟨H, hX, hHepsilon, _, _, ⟨R⟩⟩ := hA
      have hsource : (F.event T hT).pre_identify t ''
          closure (connectedComponentIn (F.event T hT).retained_preᶜ (x c).val) ⊆ H.X :=
        (hregion c).symm.subset.trans hX.symm.subset
      rcases repaired_a21_region_cases R with htwo | hdouble | hcap | hcapped | htube | hfib
      · obtain ⟨kind, U, cap₁, cap₂, C, hunion, hcontains, _⟩ := htwo
        exact closed_certificate_incident_assembly F T hT P (x c) t C
          (hsource.trans hcontains)
      · obtain ⟨tube, kind, C, hcontains, _⟩ := hdouble
        exact closed_certificate_incident_assembly F T hT P (x c) t C
          (hsource.trans hcontains)
      · obtain ⟨cap, hcontains, _⟩ := hcap
        obtain ⟨hs, ha⟩ := spaceform_incident_assembly_of_cap F T hT P (x c) t cap
          (hsource.trans hcontains)
        exact ⟨1, fun _ => _, fun _ => (Classical.choice hs).compact,
          fun _ => (Classical.choice hs).connected, fun _ => Or.inr hs, ha⟩
      · obtain ⟨tube, hcontains, hRregion⟩ := hcapped
        have hcompat := R.compatible
        rw [hRregion] at hcompat
        have hcap : tube.cap.epsilon ≤ eta := calc
          tube.cap.epsilon = H.epsilon := hcompat.1
          _ = F.parameters.epsilon := hHepsilon
          _ ≤ min N.epsilon₀ eta := hepsilon
          _ ≤ eta := min_le_right _ _
        obtain ⟨hs, ha⟩ := habsorb F T hT P (x c) t tube hcap
          (hsource.trans hcontains)
        exact ⟨1, fun _ => _, fun _ => (Classical.choice hs).compact,
          fun _ => (Classical.choice hs).connected, fun _ => Or.inr hs, ha⟩
      · obtain ⟨tube, _⟩ := htube
        obtain ⟨hs, ha⟩ := spherical_incident_assembly_of_tube F T hT P (x c) t
          tube.carrier_open tube.cylinder (hsource.trans tube.contains_X)
        exact ⟨1, fun _ => _, fun _ => (Classical.choice hs).compact,
          fun _ => (Classical.choice hs).connected, fun _ => Or.inr hs, ha⟩
      · obtain ⟨fibration, _⟩ := hfib
        obtain ⟨hs, ha⟩ := sphereBundle_incident_assembly_of_fibration F T hT P (x c) t
          fibration (hsource.trans fibration.contains_X)
        exact ⟨1, fun _ => _,
          fun _ => componentCarrier_compact _ (cappedDiscardedCarrier_compact F T hT P) _,
          fun _ => componentCarrier_connected _ _, fun _ => hs, ha⟩
    · obtain ⟨C, hcontains⟩ := hC
      obtain ⟨hs, ha⟩ := spaceform_incident_assembly_of_c_component F T hT P (x c) t C
        ((hregion c).symm.subset.trans hcontains)
      exact ⟨1, fun _ => _, fun _ => (Classical.choice hs).compact,
        fun _ => (Classical.choice hs).connected, fun _ => Or.inr hs, ha⟩
    · obtain ⟨C, hcontains⟩ := hR
      obtain ⟨hs, ha⟩ := spaceform_incident_assembly_of_round_component F T hT P (x c) t C
        ((hregion c).symm.subset.trans hcontains)
      exact ⟨1, fun _ => _, fun _ => (Classical.choice hs).compact,
        fun _ => (Classical.choice hs).connected, fun _ => Or.inr hs, ha⟩

end PoincareConjecture.M38
