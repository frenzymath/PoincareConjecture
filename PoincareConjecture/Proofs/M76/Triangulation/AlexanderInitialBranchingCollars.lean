import PoincareConjecture.Proofs.M76.Triangulation.AlexanderInitialGeometry
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBranchingCollars










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_initial_alexanderSectionProfile_with_branchingCollars
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
      W.HasBranchingCollars := by
  obtain ⟨W, hWK, hWA, hsupport, hfinite, hsigns, hgeometry⟩ :=
    K.exists_initial_alexanderSectionProfile_with_collars A hK hA hpure hcofaces
  refine ⟨W, hWK, hWA, hsupport, hfinite, hsigns, ?_⟩
  intro c hc
  obtain ⟨m, n, P, q, hm, _, _, hP, hfull, hpair, hbranch, hcount, hacc, hcollars⟩ :=
    hgeometry c hc
  refine ⟨m, n, P, q, hm, hP, ?_, hpair, hbranch, hcount, ?_, ?_⟩
  · simpa only [hWK, hWA] using hfull
  · simpa only [hWK, hWA] using hacc
  · intro ε hε
    obtain ⟨β, hβ, γ, hγ, ⟨M⟩, ⟨Mneg⟩⟩ := hcollars ε hε
    refine ⟨β, hβ, γ, hγ, ?_, ?_⟩
    · simpa only [hWK, hWA] using Nonempty.intro M.toCollarSlab
    · simpa only [hWK, hWA] using Nonempty.intro Mneg.toCollarSlab

end Geometry.SimplicialComplex
