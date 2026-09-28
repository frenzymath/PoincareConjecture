import PoincareConjecture.Definitions.M72TopologyTransport

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem m72TransportImage {X : Type*}
    {A B : GeneralizedSliceCarrier.{u}}
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (f : X → A.carrier) (U : Set X) :
    (d ∘ f) '' U = d.symm ⁻¹' (f '' U) := by
  rw [Set.image_comp, d.image_eq_preimage_symm]

theorem SmoothConnectedSumStep.transportSource
    {A A' B : GeneralizedSliceCarrier.{u}}
    (h : SmoothConnectedSumStep A B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞) :
    SmoothConnectedSumStep A' B := by
  rcases h with ⟨P, Q, ⟨D⟩, hS⟩
  exact ⟨P, Q, ⟨D.transportTarget d.symm⟩, hS⟩

theorem SmoothConnectedSumStep.reflTransGen_transportSource
    {A A' B C : GeneralizedSliceCarrier.{u}}
    (hFirst : SmoothConnectedSumStep A B)
    (hRest : Relation.ReflTransGen SmoothConnectedSumStep B C)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞) :
    Relation.ReflTransGen SmoothConnectedSumStep A' C :=
  hRest.head (hFirst.transportSource d)

theorem SmoothConnectedSumStep.reflTransGen_transportSource_of_ne
    {A A' C : GeneralizedSliceCarrier.{u}}
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C)
    (hAC : A ≠ C)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞) :
    Relation.ReflTransGen SmoothConnectedSumStep A' C := by
  rcases h.cases_head with heq | ⟨B, hFirst, hRest⟩
  · exact False.elim (hAC heq)
  · exact hFirst.reflTransGen_transportSource hRest d

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

noncomputable def SmoothFiniteConnectedSumAssembly.compOperations
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A A' C : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces A')
    (d : Diffeomorph (𝓡 3) (𝓡 3) A'.carrier A.carrier ∞)
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) :
    SmoothFiniteConnectedSumAssembly pieces C :=
  Classical.choice (S.nonempty_compOperations d h)

end PoincareConjecture
