import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.DirectedEndpoints











set_option autoImplicit false

open AbstractSimplicialComplex

namespace PoincareConjecture.M76

open PreAbstractSimplicialComplex.ModTwoCochains

open Classical in
theorem exists_residual_dart_endpoint_reversal
    {V : Type*} [Fintype V]
    (A : PreAbstractSimplicialComplex V)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (number : V ↪ ℕ)
    (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (hordered : ∀ t, StrictMono (number ∘ p t))
    (sigma : Triangle A → ZMod 2)
    (hcancel : ∀ t u : Triangle A, t ≠ u → ∀ s : Edge A,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1)
    (e : Edge A) :
    ∃ d : SurfaceDart A, d.1 = e ∧
      surfaceDartStart A p hp himage sigma (surfaceEdgePairing A hcofaces d) =
        surfaceDartEnd A p hp himage sigma d ∧
      surfaceDartEnd A p hp himage sigma (surfaceEdgePairing A hcofaces d) =
        surfaceDartStart A p hp himage sigma d := by
  have hpos : 0 < (triangleCofaces A e).card := by
    rw [hcofaces e]
    decide
  obtain ⟨t, ht⟩ := (Finset.card_pos.mp hpos)
  let d : SurfaceDart A := ⟨e, ⟨t, ht⟩⟩
  refine ⟨d, rfl, ?_⟩
  exact surfaceEdgePairing_reverses_endpoints A number p hp himage hordered sigma
    hcancel hcofaces d

end PoincareConjecture.M76
