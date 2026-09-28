import PoincareConjecture.Proofs.M76.Wall.Mathlib.RelativeFilledFrontier
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem PLDomain.of_protected_local_agreement
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R K L S : Set X}
    (hR : PLDomain e R) (hK : PLDomain e K)
    (hL : IsClosed L) (hLR : L ⊆ R) (hS : S ⊆ interior R)
    (hSK : S ⊆ frontier K)
    (hprotect : (Subtype.val : R → X) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → X) ⁻¹' L))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' L) =
      (Subtype.val : R → X) ⁻¹' S)
    (hlocal : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ L ↔ y ∈ K) :
    PLDomain e L ∧ frontier L = frontier R ∪ S := by
  have hfront := Set.protected_frontier_eq_of_relative_frontier
    hR.closed hL hLR hS hprotect hrel
  refine ⟨⟨hR.cover, hR.compatible, hL, ?_⟩, hfront⟩
  intro x hx
  rw [hfront] at hx
  rcases hx with hxR | hxS
  · have hxmem : x ∈ R := hR.closed.frontier_subset hxR
    obtain ⟨U, hU, hxU, hUL⟩ := Set.exists_open_eq_of_relative_interior
      (Subset.rfl : L ⊆ L) hLR (⟨x, hxmem⟩ : R) (hprotect hxR)
    obtain ⟨ell, v, B, hv, hxB, hzero, hBe, hhalf⟩ := hR.halfspace x hxR
    refine ⟨ell, v, B.restrOpen U hU, hv, ⟨hxB, hxU⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right B (hBe i) hU
    · intro y hy
      exact (hUL y hy.2).trans (hhalf y hy.1)
  · obtain ⟨U, hU, hxU, hUL⟩ := hlocal x hxS
    obtain ⟨ell, v, B, hv, hxB, hzero, hBe, hhalf⟩ := hK.halfspace x (hSK hxS)
    refine ⟨ell, v, B.restrOpen U hU, hv, ⟨hxB, hxU⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right B (hBe i) hU
    · intro y hy
      exact (hUL y hy.2).trans (hhalf y hy.1)

end PoincareConjecture.M76
