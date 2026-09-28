import PoincareConjecture.Definitions.M67

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

noncomputable def m67ComponentIdentification {U : GeneralizedSliceCarrier.{u}}
    (C₁ C₂ : SurgerySelectedComponent U) (h : C₂ = C₁) :
    Diffeomorph (𝓡 3) (𝓡 3) C₁.carrier.carrier C₂.carrier.carrier ∞ := by
  subst C₂
  exact Diffeomorph.refl (𝓡 3) C₁.carrier.carrier ∞

theorem m67ComponentIdentification_inclusion {U : GeneralizedSliceCarrier.{u}}
    (C₁ C₂ : SurgerySelectedComponent U) (h : C₂ = C₁) (x) :
    C₂.inclusion (m67ComponentIdentification C₁ C₂ h x) = C₁.inclusion x := by
  subst C₂
  rfl

theorem m67ComponentIdentification_basepoint {U : GeneralizedSliceCarrier.{u}}
    (C₁ C₂ : SurgerySelectedComponent U) (h : C₂ = C₁) :
    m67ComponentIdentification C₁ C₂ h C₁.basepoint = C₂.basepoint := by
  subst C₂
  rfl

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow} {T : ℝ}
  {P : RepairedComponentPath D.flow T W}
  {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
  (H : RepairedAncestryTransportInput D W P K C)
  (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
  (hpost : Nonempty (D.flow.slice S.1).carrier)

def m67EventPreTime : Set.Icc (0 : ℝ) T :=
  ⟨(D.flow.event S.1 hS).tMinus,
    (D.flow.event S.1 hS).tMinus_nonnegative,
    (D.flow.event S.1 hS).tMinus_lt.le.trans S.2.2⟩

noncomputable def m67EventParentIdentification :
    Diffeomorph (𝓡 3) (𝓡 3)
      (P.component (m67EventPreTime S hS hpost)).carrier.carrier
      (H.event_input S hS hpost).parent.carrier.carrier ∞ :=
  m67ComponentIdentification _ _ (eq_of_heq (H.event_parent_path S hS hpost))

theorem m67EventParentIdentification_inclusion (x) :
    (H.event_input S hS hpost).parent.inclusion
      (m67EventParentIdentification H S hS hpost x) =
      (P.component (m67EventPreTime S hS hpost)).inclusion x :=
  m67ComponentIdentification_inclusion _ _ _ x

theorem m67EventParentIdentification_basepoint :
    m67EventParentIdentification H S hS hpost
      (P.component (m67EventPreTime S hS hpost)).basepoint =
      (H.event_input S hS hpost).parent.basepoint :=
  m67ComponentIdentification_basepoint _ _ _

noncomputable def m67EventPreToParent
    (s : Set.Icc (0 : ℝ) T)
    (hs : (D.flow.event S.1 hS).tMinus < s.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event S.1 hS).tMinus s.1)) :
    Diffeomorph (𝓡 3) (𝓡 3) (P.component s).carrier.carrier
      (H.event_input S hS hpost).parent.carrier.carrier ∞ :=
  (P.regular_transport (m67EventPreTime S hS hpost) s hs hJ).symm.trans
    (m67EventParentIdentification H S hS hpost)

theorem m67_event_regular_ambient
    (s : Set.Icc (0 : ℝ) T)
    (hs : (D.flow.event S.1 hS).tMinus < s.1) (hsS : s.1 < S.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event S.1 hS).tMinus s.1))
    (x : (P.component (m67EventPreTime S hS hpost)).carrier.carrier) :
    (P.component s).inclusion
        (P.regular_transport (m67EventPreTime S hS hpost) s hs hJ x) =
      (D.flow.event S.1 hS).pre_identify ⟨s.1, hs.le, hsS⟩
        ((P.component (m67EventPreTime S hS hpost)).inclusion x) := by
  rw [P.regular_transport_ambient]
  have hcompat := D.flow.event_slab_compatibility S.1 hS
    (D.flow.event S.1 hS).tMinus s.1 hs
    (fun t ht => P.time_subset ⟨(D.flow.event S.1 hS).tMinus_nonnegative.trans ht.1,
      ht.2.trans s.2.2⟩) hJ
    (D.flow.event S.1 hS).tMinus s.1 ⟨le_rfl, hs.le⟩ ⟨hs.le, le_rfl⟩
    ⟨le_rfl, (D.flow.event S.1 hS).tMinus_lt⟩ ⟨hs.le, hsS⟩
    ((P.component (m67EventPreTime S hS hpost)).inclusion x)
  rw [(D.flow.event S.1 hS).pre_initial] at hcompat
  exact hcompat

theorem m67EventPreToParent_ambient
    (s : Set.Icc (0 : ℝ) T)
    (hs : (D.flow.event S.1 hS).tMinus < s.1) (hsS : s.1 < S.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event S.1 hS).tMinus s.1))
    (x : (P.component s).carrier.carrier) :
    (D.flow.event S.1 hS).pre_identify ⟨s.1, hs.le, hsS⟩
      ((H.event_input S hS hpost).parent.inclusion
        (m67EventPreToParent H S hS hpost s hs hJ x)) =
      (P.component s).inclusion x := by
  change (D.flow.event S.1 hS).pre_identify _
    ((H.event_input S hS hpost).parent.inclusion
      (m67EventParentIdentification H S hS hpost
        ((P.regular_transport (m67EventPreTime S hS hpost) s hs hJ).symm x))) = _
  rw [m67EventParentIdentification_inclusion]
  rw [← m67_event_regular_ambient S hS hpost s hs hsS hJ]
  rw [Diffeomorph.apply_symm_apply]

end PoincareConjecture
