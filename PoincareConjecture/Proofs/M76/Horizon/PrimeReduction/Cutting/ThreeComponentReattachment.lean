import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ThreeComponentNoModelChoice
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortComponentCarriers

set_option autoImplicit false
open Set

namespace Topology

theorem exists_three_component_reattachment_without_models
    {X : Type*} [TopologicalSpace X] {Q S : Set X} [LocallyConnectedSpace Q]
    (M : Set X → Prop) (hQ : IsClosed Q) (hS : IsClosed S) (hSc : IsConnected S)
    (a : Bool → X) (ha : ∀ b, a b ∈ Q ∩ S)
    (hSattach : Q ∩ S ⊆ connectedComponentIn Q (a false) ∪ connectedComponentIn Q (a true))
    (u : X) (hu : u ∈ Q)
    (hcover : Q = connectedComponentIn Q u ∪
      (connectedComponentIn Q (a false) ∪ connectedComponentIn Q (a true)))
    (H : Bool → Set X) (hH : ∀ b, IsClosed (H b)) (hHc : ∀ b, IsConnected (H b))
    (v : Bool → Bool → X) (hv : ∀ b d, v b d ∈ Q ∩ H b)
    (hv0 : ∀ b, connectedComponentIn Q (v b false) = connectedComponentIn Q u)
    (hv1 : ∀ b, connectedComponentIn Q (v b true) = connectedComponentIn Q (a b))
    (hHattach : ∀ b, Q ∩ H b ⊆
      connectedComponentIn Q (v b false) ∪ connectedComponentIn Q (v b true))
    (hOld : ∀ x ∈ Q ∪ S, ¬ M (connectedComponentIn (Q ∪ S) x))
    (hOldModel : Disjoint (connectedComponentIn Q (a false)) (connectedComponentIn Q (a true)) →
      M (connectedComponentIn Q (a false)) → M (connectedComponentIn Q (a true)) →
      M (connectedComponentIn (Q ∪ S) (a false)))
    (hRestrict : ∀ b, M (connectedComponentIn (Q ∪ H b) (v b false)) →
      M (connectedComponentIn Q u) ∧ M (connectedComponentIn Q (a b)))
    (hSelf : ∀ b, connectedComponentIn Q u = connectedComponentIn Q (a b) →
      ¬ M (connectedComponentIn (Q ∪ H b) (v b false))) :
    ∃ b, ∀ x ∈ Q ∪ H b, ¬ M (connectedComponentIn (Q ∪ H b) x) := by
  classical
  let C := connectedComponentIn Q u
  let D := fun b => connectedComponentIn Q (a b)
  have hsep : D false ≠ D true → ¬ (M (D false) ∧ M (D true)) := by
    intro hne hm
    have hd : Disjoint (D false) (D true) := disjoint_left.mpr (by
      intro x hx hy
      exact hne ((connectedComponentIn_eq hx).trans (connectedComponentIn_eq hy).symm))
    exact hOld (a false) (Or.inl (ha false).1) (hOldModel hd hm.1 hm.2)
  have hother : C ≠ D false → C ≠ D true → ¬ M C := by
    intro h0 h1 hm
    have humiss : u ∉ D false ∪ D true := by
      rintro (hx | hx)
      · exact h0 (connectedComponentIn_eq hx).symm
      · exact h1 (connectedComponentIn_eq hx).symm
    have heq := componentIn_closed_two_port_attachment_eq_of_not_mem
      hQ hS hSc (ha false) (ha true) hSattach hu humiss
    exact hOld u (Or.inl hu) (heq.symm ▸ hm)
  obtain ⟨b, hchosen, hspare⟩ :=
    PoincareConjecture.M76.exists_three_component_no_model_choice M C D hsep hother
  have hbad : ¬ M (connectedComponentIn (Q ∪ H b) (v b false)) := by
    intro hm
    rcases hchosen with heq | hbadC | hbadD
    · exact hSelf b heq hm
    · exact hbadC (hRestrict b hm).1
    · exact hbadD (hRestrict b hm).2
  have hmerged := componentIn_closed_two_port_attachment hQ (hH b) (hHc b)
    (hv b false) (hv b true) (hHattach b)
  rw [hv0 b, hv1 b] at hmerged
  refine ⟨b, ?_⟩
  intro x hx hm
  by_cases hxmerged : x ∈ connectedComponentIn (Q ∪ H b) (v b false)
  · exact hbad ((connectedComponentIn_eq hxmerged).symm ▸ hm)
  have hxQ : x ∈ Q := hx.resolve_right (fun hxH => hxmerged
    (hmerged.symm.subset (Or.inr hxH)))
  have hxmiss : x ∉ C ∪ D b := fun h => hxmerged (hmerged.symm.subset (Or.inl h))
  have heq := componentIn_closed_two_port_attachment_eq_of_not_mem
    hQ (hH b) (hHc b) (hv b false) (hv b true) (hHattach b) hxQ
    (by simpa only [hv0 b, hv1 b] using hxmiss)
  have hxother : x ∈ D (!b) := by
    have hxparts := hcover.subset hxQ
    rcases hxparts with hxC | hx0 | hx1
    · exact False.elim (hxmiss (Or.inl hxC))
    · cases b
      · exact False.elim (hxmiss (Or.inr hx0))
      · exact hx0
    · cases b
      · exact hx1
      · exact False.elim (hxmiss (Or.inr hx1))
  rcases hspare with hC | hD | hbadOther
  · exact hxmiss (Or.inl (hC ▸ hxother))
  · exact hxmiss (Or.inr (hD ▸ hxother))
  · apply hbadOther
    change M (connectedComponentIn Q (a (!b)))
    rw [connectedComponentIn_eq hxother]
    exact heq ▸ hm

end Topology
