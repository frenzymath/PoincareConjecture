import PoincareConjecture.Proofs.M76.Triangulation.AlexanderInitialBranchingCollars
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderNonisolatedProfileSigns










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_initial_alexanderSectionProfile_with_nonisolated_signs
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite)
    (hA : InjOn A K.vertices)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) :
    ∃ W : AlexanderSectionProfile E,
      W.carrier = K.space ∧ W.height = A ∧
      Function.support W.charge ⊆ A '' K.vertices ∧
      (A '' K.vertices).Finite ∧
      (∀ x ∈ W.carrier, A x ∉ A '' K.vertices →
        x ∈ closure (W.carrier ∩ {y | A y < A x}) ∧
          x ∈ closure (W.carrier ∩ {y | A x < A y})) ∧
      W.HasBranchingCollars ∧ W.HasNonisolatedHeightSigns := by
  obtain ⟨W, hWK, hWA, hsupport, hfinite, hsigns, hbranch⟩ :=
    K.exists_initial_alexanderSectionProfile_with_branchingCollars A hK hA hpure hcofaces
  refine ⟨W, hWK, hWA, hsupport, hfinite, hsigns, hbranch, ?_⟩
  exact W.hasNonisolatedHeightSigns_of_generic_complex K hK hWK (hWA.symm ▸ hA)

end Geometry.SimplicialComplex
