import PoincareLib.Topology.Manifold.ConnectedSum.Transport

/-!
# Transport at the source of reconstruction operations

When the later surgery has already been reconstructed, Corollary 15.4
identifies its whole reconstructed carrier with the survivor part of the
earlier event. This file changes the source of the first genuine connected
sum and composes the remaining operations. The reflexive relation case is
handled by transporting its disjoint union, as in the target transport API.

Source: Morgan--Tian Corollary 15.4, pp. 358--359.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

/-- Image under a postcomposed diffeomorphism, in preimage form.

This is the set identity used for transported collars and region maps in
the assembly in MT Corollary 15.4, pp. 358--359. -/
theorem m72TransportImage {X : Type*}
    {A B : GeneralizedSliceCarrier.{u}}
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (f : X → A.carrier) (U : Set X) :
    (d ∘ f) '' U = d.symm ⁻¹' (f '' U) := by
  rw [Set.image_comp, d.image_eq_preimage_symm]

/-- Change the source of one connected-sum operation by transporting its
two-piece decomposition. Source: MT Corollary 15.4, pp. 358--359. -/
theorem SmoothConnectedSumStep.transportSource
    {A A' B : GeneralizedSliceCarrier.{u}}
    (h : SmoothConnectedSumStep A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞) :
    SmoothConnectedSumStep A' B := by
  rcases h with ⟨P, Q, ⟨D⟩, hS⟩
  exact ⟨P, Q, ⟨D.transportTarget d.symm⟩, hS⟩

/-- Change the source of a chain with a displayed first operation.

The first operation witnesses that the chain is non-reflexive, so no
additional equivalence step is inserted. Source: MT Corollary 15.4,
pp. 358--359. -/
theorem SmoothConnectedSumStep.reflTransGen_transportSource
    {A A' B C : GeneralizedSliceCarrier.{u}}
    (hFirst : SmoothConnectedSumStep A B)
    (hRest : Relation.ReflTransGen SmoothConnectedSumStep B C)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞) :
    Relation.ReflTransGen SmoothConnectedSumStep A' C :=
  hRest.head (hFirst.transportSource d)

/-- Change a relation's source when its endpoints are distinct; a distinct
endpoint guarantees a genuine first operation. Source: MT Corollary 15.4,
pp. 358--359. -/
theorem SmoothConnectedSumStep.reflTransGen_transportSource_of_ne
    {A A' C : GeneralizedSliceCarrier.{u}}
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C)
    (hAC : A ≠ C)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞) :
    Relation.ReflTransGen SmoothConnectedSumStep A' C := by
  rcases h.cases_head with heq | ⟨B, hFirst, hRest⟩
  · exact False.elim (hAC heq)
  · exact hFirst.reflTransGen_transportSource hRest d

/-- Compose a reconstructed source with the operation chain of an earlier
event through a source diffeomorphism. The reflexive chain is accounted for
by target transport, rather than asserting that diffeomorphisms are
connected-sum operations. Source: MT Corollary 15.4, pp. 358--359. -/
theorem SmoothFiniteConnectedSumAssembly.nonempty_compOperations
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A A' C : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces A')
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞)
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) :
    Nonempty (SmoothFiniteConnectedSumAssembly pieces C) := by
  rcases h.cases_head with heq | ⟨B, hFirst, hRest⟩
  · subst C
    exact ⟨S.transportTarget d⟩
  · exact ⟨{
      initial := S.initial
      disjoint_union := S.disjoint_union
      operations := S.operations.trans
        (hFirst.reflTransGen_transportSource hRest d) }⟩

/-- The finite assembly obtained by composing across an actual source
diffeomorphism. Source: MT Corollary 15.4, pp. 358--359. -/
noncomputable def SmoothFiniteConnectedSumAssembly.compOperations
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A A' C : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces A')
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞)
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) :
    SmoothFiniteConnectedSumAssembly pieces C :=
  Classical.choice (S.nonempty_compOperations d h)

end PoincareMT
