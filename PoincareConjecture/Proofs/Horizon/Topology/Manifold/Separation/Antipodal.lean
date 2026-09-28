import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.DomainIdentification









set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]



theorem disjoint_closure_involutive_side (τ : X ≃ₜ X) (hτ : Function.Involutive τ)
    {A B S : Set X} (hA : IsOpen A) (hB : IsOpen B) (hcA : IsConnected A)
    (hdis : Disjoint A B) (hfront : frontier A = S) (hS : S.Nonempty)
    (hpaired : τ '' S ⊆ B) : Disjoint (closure A) (τ '' closure A) := by
  have hclB : closure A ⊆ Bᶜ :=
    closure_minimal (disjoint_left.mp hdis) hB.isClosed_compl
  have havoid : Disjoint (closure A) (τ '' S) :=
    disjoint_left.mpr fun _ hx hy => hclB hx (hpaired hy)
  apply disjoint_left.mpr
  intro x hx hxτ
  have hmeet : (closure A ∩ τ '' A).Nonempty := by
    obtain ⟨y, hy, rfl⟩ := hxτ
    have hyA : y ∈ A := by
      by_contra hyA
      have hyS : y ∈ S := hfront ▸ (hA.frontier_eq.symm ▸ ⟨hy, hyA⟩)
      exact disjoint_left.mp havoid hx (mem_image_of_mem τ hyS)
    exact ⟨τ y, hx, mem_image_of_mem τ hyA⟩
  have hsub : closure A ⊆ τ '' A :=
    subset_of_isPreconnected_of_disjoint_frontier (τ.isOpenMap A hA)
      hcA.closure.isPreconnected
      (by rw [← τ.image_frontier, hfront]; exact havoid) hmeet
  obtain ⟨z, hz⟩ := hS
  have hzcl : z ∈ closure A := frontier_subset_closure (hfront.symm ▸ hz)
  obtain ⟨y, hy, hyz⟩ := hsub hzcl
  have hτz : τ z ∈ A := by rw [← hyz, hτ]; exact hy
  obtain ⟨w, hw, hwz⟩ := hsub (subset_closure hτz)
  have hzw : z = w := by
    have heq := congrArg τ hwz
    exact (hτ z).symm.trans (heq.symm.trans (hτ w))
  have hzA : z ∈ A := hzw ▸ hw
  exact (hA.frontier_eq ▸ (hfront.symm ▸ hz)).2 hzA



theorem exists_disjoint_involutive_side (τ : X ≃ₜ X) (hτ : Function.Involutive τ)
    {A B S : Set X} (hA : IsOpen A) (hB : IsOpen B)
    (hcA : IsConnected A) (hcB : IsConnected B) (hcS : IsConnected S)
    (hdis : Disjoint A B) (hcover : A ∪ B = Sᶜ)
    (hfrontA : frontier A = S) (hfrontB : frontier B = S)
    (hSS : Disjoint S (τ '' S)) :
    (Disjoint (closure A) (τ '' closure A) ∧ τ '' S ⊆ B) ∨
      (Disjoint (closure B) (τ '' closure B) ∧ τ '' S ⊆ A) := by
  have hcτS : IsPreconnected (τ '' S) :=
    (hcS.image τ τ.continuous.continuousOn).isPreconnected
  have hsub : τ '' S ⊆ A ∪ B := by
    rw [hcover]
    exact disjoint_right.mp hSS
  rcases hcτS.subset_or_subset hA hB hdis hsub with hside | hside
  · exact Or.inr ⟨disjoint_closure_involutive_side τ hτ hB hA hcB hdis.symm
      hfrontB hcS.nonempty hside, hside⟩
  · exact Or.inl ⟨disjoint_closure_involutive_side τ hτ hA hB hcA hdis
      hfrontA hcS.nonempty hside, hside⟩

end Poincare.Topology
