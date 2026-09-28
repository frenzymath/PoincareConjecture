import PoincareConjecture.Proofs.M56.ComponentTrace
import PoincareConjecture.Proofs.M56.EqualRangeDiffeomorph









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



noncomputable def m56TraceComponents {F : SurgeryFlowData.{u}} {T : ℝ}
    (P : M56ComponentTrace F T) (C0 : SurgerySelectedComponent (F.slice 0))
    (s : Icc (0 : ℝ) T) : SurgerySelectedComponent (F.slice s.1) := by
  classical
  exact if h : s.1 = 0 then h.symm ▸ C0
    else m56SelectedComponent (F.slices_compact s.1 (P.time_subset s.2)) (P.point s)



theorem m56TraceComponents_zero {F : SurgeryFlowData.{u}} {T : ℝ}
    (P : M56ComponentTrace F T) (C0 : SurgerySelectedComponent (F.slice 0)) (hT : 0 ≤ T) :
    m56TraceComponents P C0 ⟨0, le_rfl, hT⟩ = C0 := by
  simp only [m56TraceComponents, ↓reduceDIte]



theorem m56TraceComponents_range {F : SurgeryFlowData.{u}} {T : ℝ}
    (P : M56ComponentTrace F T) (C0 : SurgerySelectedComponent (F.slice 0))
    (hC0 : range C0.inclusion = univ)
    (hconn : IsConnected (univ : Set (F.slice 0).carrier)) (s : Icc (0 : ℝ) T) :
    range (m56TraceComponents P C0 s).inclusion = connectedComponent (P.point s) := by
  classical
  by_cases hs : s.1 = 0
  · obtain ⟨s, hs0, hsT⟩ := s
    dsimp at hs
    subst s
    rw [m56TraceComponents_zero P C0 hsT, hC0]
    let : ConnectedSpace (F.slice 0).carrier := connectedSpace_iff_univ.mpr hconn
    exact (PreconnectedSpace.connectedComponent_eq_univ _).symm
  · rw [m56TraceComponents, dif_neg hs]
    exact m56SelectedComponent_range (F.slices_compact s.1 (P.time_subset s.2)) (P.point s)



theorem m56ComponentDiffeomorph_exists {A B : GeneralizedSliceCarrier.{u}}
    (P : SurgerySelectedComponent A) (Q : SurgerySelectedComponent B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (x : A.carrier) (y : B.carrier)
    (hP : range P.inclusion = connectedComponent x)
    (hQ : range Q.inclusion = connectedComponent y)
    (h : ConnectedComponents.mk (d x) = ConnectedComponents.mk y) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) P.carrier.carrier Q.carrier.carrier ∞,
      ∀ z, Q.inclusion (e z) = d (P.inclusion z) := by
  have hf (z : P.carrier.carrier) : d (P.inclusion z) ∈ range Q.inclusion := by
    rw [hQ]
    have hz : P.inclusion z ∈ connectedComponent x := hP ▸ mem_range_self z
    exact ConnectedComponents.coe_eq_coe'.mp
      ((m56ComponentClass_map d.continuous (ConnectedComponents.coe_eq_coe'.mpr hz)).trans h)
  have hback : ConnectedComponents.mk (d.symm y) = ConnectedComponents.mk x := by
    have h' := m56ComponentClass_map d.symm.continuous h.symm
    simpa only [d.symm_apply_apply] using h'
  have hg (z : Q.carrier.carrier) : d.symm (Q.inclusion z) ∈ range P.inclusion := by
    rw [hP]
    have hz : Q.inclusion z ∈ connectedComponent y := hQ ▸ mem_range_self z
    exact ConnectedComponents.coe_eq_coe'.mp
      ((m56ComponentClass_map d.symm.continuous (ConnectedComponents.coe_eq_coe'.mpr hz)).trans
        hback)
  exact ⟨m56EqualRangeDiffeomorph P Q d hf hg,
    m56EqualRangeDiffeomorph_inclusion P Q d hf hg⟩



theorem m56Trace_regularDiffeomorph {F : SurgeryFlowData.{u}} {T : ℝ}
    (P : M56ComponentTrace F T)
    (C : ∀ s : Icc (0 : ℝ) T, SurgerySelectedComponent (F.slice s.1))
    (hC : ∀ s, range (C s).inclusion = connectedComponent (P.point s))
    (a b : Icc (0 : ℝ) T) (hab : a.1 < b.1)
    (hfree : Disjoint F.surgery_times (Ioc a.1 b.1)) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) (C a).carrier.carrier (C b).carrier.carrier ∞,
      ∀ x, (C b).inclusion (e x) =
        (F.regular_slabs a.1 b.1 hab
          (fun _u hu => P.time_subset ⟨a.2.1.trans hu.1, hu.2.trans b.2.2⟩) hfree).transport
          ⟨a.1, le_rfl, hab.le⟩ ⟨b.1, hab.le, le_rfl⟩ ((C a).inclusion x) := by
  let hJ : Icc a.1 b.1 ⊆ F.time_domain :=
    fun _u hu => P.time_subset ⟨a.2.1.trans hu.1, hu.2.trans b.2.2⟩
  let S := F.regular_slabs a.1 b.1 hab hJ hfree
  let d := (S.identify ⟨a.1, le_rfl, hab.le⟩).symm.trans
    (S.identify ⟨b.1, hab.le, le_rfl⟩)
  apply m56ComponentDiffeomorph_exists (C a) (C b) d (P.point a) (P.point b) (hC a) (hC b)
  have h := P.regular a.1 b.1 hab hJ hfree a b ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
  have h' := m56ComponentClass_map (S.identify ⟨b.1, hab.le, le_rfl⟩).continuous h
  change ConnectedComponents.mk
      (S.identify ⟨b.1, hab.le, le_rfl⟩ ((S.identify ⟨a.1, le_rfl, hab.le⟩).symm (P.point a))) =
    ConnectedComponents.mk
      (S.identify ⟨b.1, hab.le, le_rfl⟩ ((S.identify ⟨b.1, hab.le, le_rfl⟩).symm (P.point b))) at h'
  simpa only [d, Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.apply_symm_apply] using h'

end PoincareConjecture
