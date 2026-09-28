import PoincareConjecture.Proofs.M47.FirstFailureAttainment
import PoincareConjecture.Proofs.M47.PrefixMonotone
import PoincareConjecture.Proofs.M47.CanonicalCapSlabStability
import PoincareConjecture.Proofs.M47.CanonicalComponentSlabStability
import PoincareConjecture.Proofs.M47.CanonicalRoundSlabStability
import PoincareConjecture.Proofs.M47.CanonicalNeckExposedAlternative
import PoincareConjecture.Proofs.M47.CanonicalNeckCoveredPhysicalCap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47

theorem firstFailure_attained_of_standard_cover
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (cover : ∀ s ∈ Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        ((S.cap_persistence.standard_cap.flow.metric s).edist 0 x).toReal *
          Real.sqrt ((S.cap_persistence.standard_cap.flow.connection s).scalarCurvature x) ≤
            (57 / 10 : ℝ) * S.setup.epsilon⁻¹ →
        ∃ N : CapCertificate (S.cap_persistence.standard_cap.flow.metric s),
          N.epsilon = S.setup.epsilon ∧ N.cap_constant ≤ S.setup.C ∧
          N.connection = S.cap_persistence.standard_cap.flow.connection s ∧ x ∈ N.core)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ p.r (Fin.last p.i)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryObservationIsNextEpoch p O → SurgeryPrefixControls p F O →
        SurgeryFlowAdmissible F → SurgeryFlowPinched F →
        SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
        SurgeryPostPrefixScales p F O r delta →
        (∀ t ∈ surgeryObservationInterval O ∩
          Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta t ≤ delta) →
        ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r →
        ∃ t ∈ Ico (surgeryEpochStart p.i) O.H,
          t = sInf (canonicalFailureTimes F O r) ∧
          SurgeryCanonicalOn F (Ico 0 t) r ∧
          ∃ x : (F.slice t).carrier,
            r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
            ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
  obtain ⟨delta, hdelta, hlast, physical⟩ :=
    exists_firstFailure_exposed_physical_cap_cutoff_of_standard_cover P S p hp
      (zero_lt_one.trans_le S.setup.C_large) cover r hr hle
  refine ⟨delta, hdelta, hlast, ?_⟩
  intro F O hnext old admissible pinched _policy scales overlap hfail
  have hT0 : 0 ≤ surgeryEpochStart p.i := by unfold surgeryEpochStart; positivity
  have hold : SurgeryCanonicalOn F (Ico 0 (surgeryEpochStart p.i)) r :=
    (old.canonicalOn_prefixFinal hr hle).restrict
      (fun _ ht => ⟨⟨ht.1, ht.2.trans hnext.1⟩, ht⟩)
  obtain ⟨t, ht, hpast, b, htb, hJ, hfree, hbH, x, hscalar,
    times, points, _hanti, htimes, hpoints, hbad⟩ :=
    exists_canonicalFailureSlabLimit P.m04 hT0 hold hfail
  let slab := F.regular_slabs t b htb hJ hfree
  let t0 : Icc t b := ⟨t, le_rfl, htb.le⟩
  have htF : t ∈ F.time_domain := hJ ⟨le_rfl, htb.le⟩
  have bad := fun n => (hbad n).2
  have noCap (N : CapCertificate (F.metric t))
      (he : N.epsilon = F.parameters.epsilon) (hC : N.cap_constant ≤ F.parameters.C) :
      x ∉ N.core := by
    have h := regularSlab_limit_not_cap P.m04 slab htF t0 times points x
      htimes hpoints bad N he hC
    simpa only [t0, slab.initial_identify] using h
  have hnot : ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
    intro hcanonical
    cases hcanonical with
    | cap N he hC _hconnection hx => exact noCap N he hC hx
    | component N hx =>
        have h := regularSlab_limit_not_component P.m04 slab htF t0 times points x
          htimes hpoints bad N
        have h' : x ∉ N.carrier := by
          simpa only [t0, slab.initial_identify] using h
        exact h' hx
    | round N hx =>
        have h := regularSlab_limit_not_round slab t0 times points x htimes hpoints bad N
        have h' : x ∉ N.carrier := by
          simpa only [t0, slab.initial_identify] using h
        exact h' hx
    | neck N hcenter =>
        have hhigh : r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature N.neck.center := by
          simpa only [hcenter] using hscalar
        have hQ : r⁻¹ ^ 2 ≤ N.neck.scale⁻¹ ^ 2 := by
          rw [neck_scale_inverse_square N.neck, N.connection_eq]
          exact hhigh
        have hbottom := firstFailure_neck_bottom_after_overlap p hr hle ht.1 hQ
        have hDomain : Ico (surgeryEpochStart (p.i - 1)) O.H ⊆ F.time_domain := by
          intro s hs
          apply O.interval_subset
          exact ⟨(show 0 ≤ surgeryEpochStart (p.i - 1) by
            unfold surgeryEpochStart; positivity).trans hs.1, hs.2⟩
        have hpointsN : Tendsto points atTop (𝓝 N.neck.center) := by
          simpa only [hcenter] using hpoints
        obtain ⟨E, hagree, hbased, hSurgery, contact⟩ :=
          regularSlab_limit_strongNeck_exposed_bottom P N hbottom ht.2 hDomain
            htb hJ hfree times points htimes hpointsN bad
        let U : TopologicalSpace.Opens (F.slice t).carrier :=
          ⟨N.neck.carrier, N.neck.carrier_open⟩
        let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
        have ha : a ∈ Icc a 0 :=
          ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
        let : Nonempty (F.slice (t + a / 1)).carrier := ⟨E.forward a ha N.neck.center⟩
        obtain ⟨i, z, hzImage, hzCap⟩ := contact
        obtain ⟨y, hy, hyz⟩ := hzImage
        have hyCap : E.forward a ha y ∈ ((F.event (t + a / 1) hSurgery).caps i).carrier :=
          hyz.symm ▸ hzCap
        obtain ⟨H, hHe, hHC, _hHD, hcore⟩ := physical F O hnext.2 old admissible pinched
          scales (fun s hs => overlap s ⟨hs.1, hs.2.1, hs.1.2⟩) t ht hpast N hhigh
            U rfl E hbased hagree hSurgery i ⟨y, hy⟩ hyCap
        have hepsilon : H.epsilon = F.parameters.epsilon := by
          rw [old.epsilon_eq, hp.setup_eq]
          exact hHe
        have hconstant : H.cap_constant ≤ F.parameters.C := by
          rw [old.C_eq, hp.setup_eq]
          exact hHC
        exact noCap H hepsilon hconstant (by simpa only [hcenter] using hcore)
  have htbad : t ∈ canonicalFailureTimes F O r :=
    ⟨⟨hT0.trans ht.1, ht.2⟩, x, hscalar, hnot⟩
  have hbound : ∀ s ∈ canonicalFailureTimes F O r, t ≤ s :=
    canonicalFailureTimes_lower_bound hpast
  have hinf : t = sInf (canonicalFailureTimes F O r) :=
    le_antisymm (le_csInf ⟨t, htbad⟩ hbound) (csInf_le ⟨t, hbound⟩ htbad)
  exact ⟨t, ht, hinf, hpast, x, hscalar, hnot⟩

end PoincareConjecture.Proofs.M47
