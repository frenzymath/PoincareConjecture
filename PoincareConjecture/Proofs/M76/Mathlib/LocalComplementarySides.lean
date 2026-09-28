import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Topology

variable {X : Type*} [TopologicalSpace X]

def Set.HasLocalComplementarySides (A : Set X) : Prop :=
  ∀ a ∈ A, ∃ U L R : Set X, IsOpen U ∧ a ∈ U ∧
    IsPreconnected L ∧ IsPreconnected R ∧ U \ A = L ∪ R ∧
    A ∩ U ⊆ closure L ∧ A ∩ U ⊆ closure R

theorem IsPreconnected.subset_connectedComponentIn_of_inter_nonempty
    {A S : Set X} {x : X} (hS : IsPreconnected S) (hSA : S ⊆ A)
    (hinter : (S ∩ _root_.connectedComponentIn A x).Nonempty) :
    S ⊆ _root_.connectedComponentIn A x := by
  obtain ⟨y, hyS, hyC⟩ := hinter
  rw [connectedComponentIn_eq hyC]
  exact hS.subset_connectedComponentIn hyS hSA

variable [LocallyConnectedSpace X]

theorem IsClosed.frontier_connectedComponentIn_compl_subset {A : Set X}
    (hA : IsClosed A) (x : X) : frontier (connectedComponentIn Aᶜ x) ⊆ A := by
  intro q hq
  by_contra hqa
  have hC : IsOpen (connectedComponentIn Aᶜ x) := hA.isOpen_compl.connectedComponentIn
  have hD : IsOpen (connectedComponentIn Aᶜ q) := hA.isOpen_compl.connectedComponentIn
  obtain ⟨y, hyD, hyC⟩ := mem_closure_iff.mp hq.1 _ hD (mem_connectedComponentIn hqa)
  have heq : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ q :=
    (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyD).symm
  exact hq.2 (by rw [hC.interior_eq, heq]; exact mem_connectedComponentIn hqa)

omit [LocallyConnectedSpace X] in

theorem Set.HasLocalComplementarySides.isOpen_component_frontier
    {A : Set X} (hsides : A.HasLocalComplementarySides) (x : X) :
    IsOpen {a : A | a.val ∈ frontier (connectedComponentIn Aᶜ x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro a ha
  obtain ⟨U, L, R, hU, haU, hL, hR, hcover, hclL, hclR⟩ := hsides a.val a.property
  have hLR : L ∪ R ⊆ Aᶜ := by
    rw [← hcover]
    exact fun _ h => h.2
  obtain ⟨y, hyU, hyC⟩ := mem_closure_iff.mp ha.1 U hU haU
  have hyLR : y ∈ L ∪ R := hcover ▸ ⟨hyU, connectedComponentIn_subset Aᶜ x hyC⟩
  have hprop (S : Set X) (hS : IsPreconnected S) (hSA : S ⊆ Aᶜ)
      (hyS : y ∈ S) (hcl : A ∩ U ⊆ closure S) :
      A ∩ U ⊆ frontier (connectedComponentIn Aᶜ x) := by
    have hSC := hS.subset_connectedComponentIn_of_inter_nonempty hSA ⟨y, hyS, hyC⟩
    intro b hb
    refine ⟨closure_mono hSC (hcl hb), ?_⟩
    intro hi
    exact connectedComponentIn_subset Aᶜ x (interior_subset hi) hb.1
  have hfront : A ∩ U ⊆ frontier (connectedComponentIn Aᶜ x) := by
    rcases hyLR with hyL | hyR
    · exact hprop L hL (subset_union_left.trans hLR) hyL hclL
    · exact hprop R hR (subset_union_right.trans hLR) hyR hclR
  exact ⟨Subtype.val ⁻¹' U, fun b hb => hfront ⟨b.property, hb⟩,
    hU.preimage continuous_subtype_val, haU⟩

variable [PreconnectedSpace X]

theorem Set.HasLocalComplementarySides.frontier_component_eq
    {A : Set X} (hsides : A.HasLocalComplementarySides) (hA : IsClosed A)
    (hconn : IsConnected A) {x : X} (hx : x ∈ Aᶜ) :
    frontier (connectedComponentIn Aᶜ x) = A := by
  let : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  have hsub := hA.frontier_connectedComponentIn_compl_subset x
  have hproper : connectedComponentIn Aᶜ x ≠ univ := by
    obtain ⟨a, ha⟩ := hconn.nonempty
    intro heq
    exact connectedComponentIn_subset Aᶜ x (by rw [heq]; trivial) ha
  obtain ⟨a, ha⟩ := nonempty_frontier_iff.mpr
    ⟨⟨x, mem_connectedComponentIn hx⟩, hproper⟩
  have hcl : IsClopen {a : A | a.val ∈ frontier (connectedComponentIn Aᶜ x)} :=
    ⟨isClosed_frontier.preimage continuous_subtype_val, hsides.isOpen_component_frontier x⟩
  have hall := hcl.eq_univ ⟨⟨a, hsub ha⟩, ha⟩
  apply hsub.antisymm
  intro b hb
  have hm : (⟨b, hb⟩ : A) ∈ {a : A | a.val ∈ frontier (connectedComponentIn Aᶜ x)} := by
    rw [hall]
    trivial
  exact hm

theorem Set.HasLocalComplementarySides.exists_two_components
    {A : Set X} (hsides : A.HasLocalComplementarySides) (hA : IsClosed A)
    (hconn : IsConnected A) :
    ∃ l ∈ Aᶜ, ∃ r ∈ Aᶜ, ∀ x ∈ Aᶜ,
      connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ l ∨
      connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ r := by
  obtain ⟨a, ha⟩ := hconn.nonempty
  obtain ⟨U, L, R, hU, haU, hL, hR, hcover, hclL, hclR⟩ := hsides a ha
  have hLR : L ∪ R ⊆ Aᶜ := by
    rw [← hcover]
    exact fun _ h => h.2
  obtain ⟨l, hl⟩ := closure_nonempty_iff.mp (show (closure L).Nonempty from ⟨a, hclL ⟨ha, haU⟩⟩)
  obtain ⟨r, hr⟩ := closure_nonempty_iff.mp (show (closure R).Nonempty from ⟨a, hclR ⟨ha, haU⟩⟩)
  refine ⟨l, hLR (Or.inl hl), r, hLR (Or.inr hr), ?_⟩
  intro x hx
  have haC : a ∈ closure (connectedComponentIn Aᶜ x) :=
    frontier_subset_closure (by rw [hsides.frontier_component_eq hA hconn hx]; exact ha)
  obtain ⟨y, hyU, hyC⟩ := mem_closure_iff.mp haC U hU haU
  have hyLR : y ∈ L ∪ R := hcover ▸ ⟨hyU, connectedComponentIn_subset Aᶜ x hyC⟩
  rcases hyLR with hyL | hyR
  · have hy := hL.subset_connectedComponentIn hl (subset_union_left.trans hLR) hyL
    exact Or.inl ((connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hy).symm)
  · have hy := hR.subset_connectedComponentIn hr (subset_union_right.trans hLR) hyR
    exact Or.inr ((connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hy).symm)
