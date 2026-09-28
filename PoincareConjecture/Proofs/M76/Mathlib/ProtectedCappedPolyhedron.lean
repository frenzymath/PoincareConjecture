import PoincareConjecture.Proofs.M76.Mathlib.ProtectedSlicePolyhedron
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs










set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]





theorem IsFinitePLBallPair.exists_protected_capped_polyhedron
    {s b d : Set X} (hs : IsFinitePLBallPair E s b) (hd : IsFinitePLBallPair F d b)
    (A : X →ᵃ[ℝ] ℝ) (q : X) (N : SimplicialComplex ℝ X) (hN : N.faces.Finite)
    (hside : d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q})
    (hdN : d ∩ N.space ⊆ {q}) (hzeros : (s ∩ {x | A x = 0}) \ b ⊆ N.space) :
    ∃ Q : SimplicialComplex ℝ X, Q.faces.Finite ∧
      Q.space = closure ((s ∪ d) ∩ {x | A x < 0}) ∪ N.space ∧
      d ∩ Q.space ⊆ {q} ∧ (s ∪ d) ∩ {x | A x < 0} ⊆ Q.space ∧
      (((s ∪ d) ∩ {x | A x = 0}) \ d) ⊆ Q.space := by
  have hscopy := hs
  have hdcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hscopy
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLd, _⟩, _⟩, _⟩ := hdcopy
  obtain ⟨J, hJ, hJspace⟩ := K.exists_finite_triangulation_union L hK hL
  rw [hKs, hLd] at hJspace
  have hcover : (((s ∪ d) ∩ {x | A x = 0}) \ d) ⊆ N.space := by
    rintro x ⟨⟨hxs | hxd, hxA⟩, hxnd⟩
    · exact hzeros ⟨⟨hxs, hxA⟩, fun hxb => hxnd (hd.1 hxb)⟩
    · exact (hxnd hxd).elim
  rw [← hJspace] at hside hcover ⊢
  exact J.exists_protected_slice_polyhedron N hJ hN A q hside hdN hcover

end Set
