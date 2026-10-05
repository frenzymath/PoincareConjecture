import Mathlib.Topology.Connected.LocallyConnected

/-!
# Complement components from local two-sided neighborhoods

General topological auxiliaries for polygonal separation in Cairns (1951),
Theorem 2.1, pp. 860-861. Connected local sides propagate the frontier of
each complement component along a closed connected set. This bounds the
number of components by two; a separate non-preconnectedness hypothesis
makes them distinct. The local hypothesis must still be proved for polygons.
See `smale/derivations/2026-09-21-local-two-sides.md` for the derivation.
-/

set_option autoImplicit false

open Set Topology

namespace Poincare.Manifold.Schoenflies.Plane

variable {X : Type*} [TopologicalSpace X]

/-- Local connected sides with common closure contact along a set; a geometric
input for the separation statement in Cairns, Theorem 2.1, pp. 860-861. -/
def HasLocalTwoSides (C : Set X) : Prop :=
  ∀ q ∈ C, ∃ W A B : Set X, IsOpen W ∧ q ∈ W ∧ IsConnected A ∧ IsConnected B ∧
    A ∪ B = W \ C ∧ C ∩ W ⊆ closure A ∧ C ∩ W ⊆ closure B

/-- Components of an open set are relatively closed in that set; the component
ingredient for Cairns, Theorem 2.1, pp. 860-861. -/
theorem closure_connectedComponentIn_inter_subset [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (x : X) :
    closure (connectedComponentIn U x) ∩ U ⊆ connectedComponentIn U x := by
  rintro z ⟨hz, hzU⟩
  obtain ⟨p, hpz, hpx⟩ := mem_closure_iff.mp hz (connectedComponentIn U z)
    hU.connectedComponentIn (mem_connectedComponentIn hzU)
  have he : connectedComponentIn U z = connectedComponentIn U x :=
    (connectedComponentIn_eq hpz).trans (connectedComponentIn_eq hpx).symm
  rw [← he]
  exact mem_connectedComponentIn hzU

/-- An open-set component has no frontier point in that open set; the frontier
ingredient for Cairns, Theorem 2.1, pp. 860-861. -/
theorem frontier_connectedComponentIn_subset_compl [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (x : X) :
    frontier (connectedComponentIn U x) ⊆ Uᶜ := by
  intro z hz hzU
  rw [hU.connectedComponentIn.frontier_eq] at hz
  exact hz.2 (closure_connectedComponentIn_inter_subset hU x ⟨hz.1, hzU⟩)

variable [PreconnectedSpace X] [LocallyConnectedSpace X] {C : Set X}

/-- Local sides force every complement component to have the full connected
boundary as frontier; auxiliary topology for Cairns, Theorem 2.1, pp. 860-861. -/
theorem HasLocalTwoSides.frontier_compl_component_eq (hloc : HasLocalTwoSides C)
    (hC : IsClosed C) (hconn : IsConnected C) {x : X} (hx : x ∉ C) :
    frontier (connectedComponentIn Cᶜ x) = C := by
  let K := connectedComponentIn Cᶜ x
  have hKopen : IsOpen K := hC.isOpen_compl.connectedComponentIn
  have hKsub : K ⊆ Cᶜ := connectedComponentIn_subset Cᶜ x
  have hDsub : frontier K ⊆ C := by
    simpa only [compl_compl] using
      frontier_connectedComponentIn_subset_compl hC.isOpen_compl x
  have hKproper : K ≠ univ := by
    intro he
    obtain ⟨q, hq⟩ := hconn.nonempty
    have hqK : q ∈ K := by rw [he]; exact mem_univ q
    exact hKsub hqK hq
  have hDne : (frontier K).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨x, mem_connectedComponentIn hx⟩, hKproper⟩
  have hlocal : ∀ q ∈ frontier K, ∃ W : Set X,
      IsOpen W ∧ q ∈ W ∧ C ∩ W ⊆ frontier K := by
    intro q hq
    obtain ⟨W, A, B, hW, hqW, hA, hB, hAB, hCA, hCB⟩ := hloc q (hDsub hq)
    obtain ⟨z, hzW, hzK⟩ :=
      mem_closure_iff.mp (frontier_subset_closure hq) W hW hqW
    have hABsub : A ∪ B ⊆ Cᶜ := by
      rw [hAB]
      exact fun _ hz => hz.2
    have habsorb : ∀ {S : Set X}, IsPreconnected S → S ⊆ Cᶜ → z ∈ S → S ⊆ K := by
      intro S hS hSU hzS
      calc
        S ⊆ connectedComponentIn Cᶜ z := hS.subset_connectedComponentIn hzS hSU
        _ = K := (connectedComponentIn_eq hzK).symm
    have hzAB : z ∈ A ∪ B := hAB.symm ▸ ⟨hzW, hKsub hzK⟩
    have hCW : C ∩ W ⊆ closure K := by
      rcases hzAB with hzA | hzB
      · exact hCA.trans (closure_mono
          (habsorb hA.isPreconnected (subset_union_left.trans hABsub) hzA))
      · exact hCB.trans (closure_mono
          (habsorb hB.isPreconnected (subset_union_right.trans hABsub) hzB))
    refine ⟨W, hW, hqW, ?_⟩
    intro p hp
    rw [hKopen.frontier_eq]
    exact ⟨hCW hp, fun hpK => hKsub hpK hp.1⟩
  have hrelopen : IsOpen ((Subtype.val : C → X) ⁻¹' frontier K) := by
    apply isOpen_iff_forall_mem_open.mpr
    intro q hq
    obtain ⟨W, hW, hqW, hCW⟩ := hlocal q hq
    exact ⟨Subtype.val ⁻¹' W, fun p hp => hCW ⟨p.property, hp⟩,
      hW.preimage continuous_subtype_val, hqW⟩
  have hrelclopen : IsClopen ((Subtype.val : C → X) ⁻¹' frontier K) :=
    ⟨isClosed_frontier.preimage continuous_subtype_val, hrelopen⟩
  have hrelne : ((Subtype.val : C → X) ⁻¹' frontier K).Nonempty := by
    obtain ⟨q, hq⟩ := hDne
    exact ⟨⟨q, hDsub hq⟩, hq⟩
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  apply subset_antisymm hDsub
  intro q hq
  have hmem : (⟨q, hq⟩ : C) ∈ (Subtype.val : C → X) ⁻¹' frontier K := by
    rw [hrelclopen.eq_univ hrelne]
    exact mem_univ _
  exact hmem

/-- Two local sides meet every global complement component; the component
upper bound for Cairns, Theorem 2.1, pp. 860-861. -/
theorem HasLocalTwoSides.exists_two_compl_components_cover (hloc : HasLocalTwoSides C)
    (hC : IsClosed C) (hconn : IsConnected C) :
    ∃ a ∈ Cᶜ, ∃ b ∈ Cᶜ, ∀ x ∈ Cᶜ,
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ a ∨
        connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ b := by
  obtain ⟨q, hq⟩ := hconn.nonempty
  obtain ⟨W, A, B, hW, hqW, hA, hB, hAB, _, _⟩ := hloc q hq
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨b, hb⟩ := hB.nonempty
  have hABsub : A ∪ B ⊆ Cᶜ := by
    rw [hAB]
    exact fun _ hz => hz.2
  refine ⟨a, hABsub (Or.inl ha), b, hABsub (Or.inr hb), ?_⟩
  intro x hx
  have hqK : q ∈ closure (connectedComponentIn Cᶜ x) :=
    frontier_subset_closure ((hloc.frontier_compl_component_eq hC hconn hx).symm ▸ hq)
  obtain ⟨z, hzW, hzK⟩ := mem_closure_iff.mp hqK W hW hqW
  have hzAB : z ∈ A ∪ B :=
    hAB.symm ▸ ⟨hzW, connectedComponentIn_subset Cᶜ x hzK⟩
  have habsorb : ∀ {S : Set X}, IsPreconnected S → S ⊆ Cᶜ → z ∈ S →
      S ⊆ connectedComponentIn Cᶜ x := by
    intro S hS hSU hzS
    calc
      S ⊆ connectedComponentIn Cᶜ z := hS.subset_connectedComponentIn hzS hSU
      _ = connectedComponentIn Cᶜ x := (connectedComponentIn_eq hzK).symm
  rcases hzAB with hzA | hzB
  · exact Or.inl (connectedComponentIn_eq
      (habsorb hA.isPreconnected (subset_union_left.trans hABsub) hzA ha))
  · exact Or.inr (connectedComponentIn_eq
      (habsorb hB.isPreconnected (subset_union_right.trans hABsub) hzB hb))

/-- A non-preconnected complement with local two-sided neighborhoods has
exactly two components; auxiliary topology for Cairns, Theorem 2.1, pp. 860-861. -/
theorem HasLocalTwoSides.exists_two_distinct_compl_components (hloc : HasLocalTwoSides C)
    (hC : IsClosed C) (hconn : IsConnected C) (hsep : ¬ IsPreconnected Cᶜ) :
    ∃ a ∈ Cᶜ, ∃ b ∈ Cᶜ,
      connectedComponentIn Cᶜ a ≠ connectedComponentIn Cᶜ b ∧
        connectedComponentIn Cᶜ a ∪ connectedComponentIn Cᶜ b = Cᶜ := by
  obtain ⟨a, ha, b, hb, hcover⟩ := hloc.exists_two_compl_components_cover hC hconn
  have hunion : connectedComponentIn Cᶜ a ∪ connectedComponentIn Cᶜ b = Cᶜ := by
    apply subset_antisymm
    · exact union_subset (connectedComponentIn_subset Cᶜ a) (connectedComponentIn_subset Cᶜ b)
    · intro x hx
      rcases hcover x hx with he | he
      · exact Or.inl (he ▸ mem_connectedComponentIn hx)
      · exact Or.inr (he ▸ mem_connectedComponentIn hx)
  refine ⟨a, ha, b, hb, ?_, hunion⟩
  intro he
  rw [he, union_self] at hunion
  exact hsep (hunion ▸ isPreconnected_connectedComponentIn)

end Poincare.Manifold.Schoenflies.Plane
