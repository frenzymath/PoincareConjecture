import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Collars.AlexanderInitialBranchingCollars
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderNonisolatedProfileSigns

/-!
# Initial branching profiles with all hereditary height signs

The same initial profile retains its finite height event
set, both signed branching collars and both strict height
approaches at every nonisolated point of every level.
See Alexander 1924, pp. 6--8 and M76 derivations 269 and 276.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual generic initial surface supplies one complete
branching profile with the stronger hereditary sign condition.
The weaker finite exceptional-height condition and its exact
original event set remain available for choosing surgery
windows. See Alexander pp. 6--8 and M76 derivation 276. -/
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
