import PoincareConjecture.Proofs.M76.Wall.ProtectedPLArc
import PoincareConjecture.Proofs.M76.Wall.Mathlib.RelativeFilledFrontier











set_option autoImplicit false

open Set Geometry

namespace Set




theorem isConnected_exterior_of_connected_relative_compl
    {X : Type*} [TopologicalSpace X] {R L : Set X}
    (hR : IsClosed R) (hBL : frontier R ⊆ L)
    (hconn : IsConnected (((Subtype.val : R → X) ⁻¹' L)ᶜ)) :
    IsConnected (interior R \ L) := by
  have himage : (Subtype.val : R → X) '' (((Subtype.val : R → X) ⁻¹' L)ᶜ) =
      R \ L := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro x ⟨hxR, hxL⟩
      exact ⟨⟨x, hxR⟩, hxL, rfl⟩
  have hconnected : IsConnected (R \ L) := by
    rw [← himage]
    exact hconn.image Subtype.val continuous_subtype_val.continuousOn
  have heq : R \ L = interior R \ L := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨?_, hx.2⟩
      by_contra hnot
      have hxB : x ∈ frontier R := by
        rw [hR.frontier_eq]
        exact ⟨hx.1, hnot⟩
      exact hx.2 (hBL hxB)
    · exact fun _ hx => ⟨interior_subset hx.1, hx.2⟩
  exact heq ▸ hconnected

end Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem PLDomain.exists_arc_in_filled_complement
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R L P : Set X}
    (hL : PLDomain e L) (hR : IsClosed R) (hP : IsClosed P)
    (hPR : P ⊆ R) (hBP : frontier R ⊆ P)
    (hprotect : (Subtype.val : R → X) ⁻¹' P ⊆
      interior ((Subtype.val : R → X) ⁻¹' L))
    (hconn : IsConnected (((Subtype.val : R → X) ⁻¹' L)ᶜ))
    {a b : X} (ha : a ∈ frontier L) (haR : a ∈ interior R)
    (hb : b ∈ frontier L) (hbR : b ∈ interior R) (hab : a ≠ b) :
    ∃ q : ℝ → X, PolyhedralPLInCharts e q (Icc (0 : ℝ) 1) ∧
      InjOn q (Icc (0 : ℝ) 1) ∧ q 0 = a ∧ q 1 = b ∧
      MapsTo q (Icc (0 : ℝ) 1) (interior R \ P) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ L ↔ t = 0 ∨ t = 1 := by
  have hPL : P ⊆ L := by
    intro x hx
    have hrel : (⟨x, hPR hx⟩ : R) ∈
        interior ((Subtype.val : R → X) ⁻¹' L) := hprotect hx
    have hmem : (⟨x, hPR hx⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' L :=
      interior_subset hrel
    exact hmem
  have havoid {x : X} (hx : x ∈ frontier L) (hxR : x ∈ interior R) : x ∉ P := by
    intro hxP
    have hrel : (⟨x, hPR hxP⟩ : R) ∈
        interior ((Subtype.val : R → X) ⁻¹' L) := hprotect hxP
    exact hx.2 ((mem_interior_subtype_preimage_iff_of_mem_interior
      (⟨x, hPR hxP⟩ : R) hxR).mp hrel)
  have hW : IsOpen (interior R \ P) := isOpen_interior.sdiff hP
  have hWconn : IsConnected ((interior R \ P) \ L) := by
    have heq : (interior R \ P) \ L = interior R \ L := by
      ext x
      constructor
      · exact fun hx => ⟨hx.1.1, hx.2⟩
      · exact fun hx => ⟨⟨hx.1, fun hxP => hx.2 (hPL hxP)⟩, hx.2⟩
    rw [heq]
    exact isConnected_exterior_of_connected_relative_compl hR (hBP.trans hPL) hconn
  exact hL.exists_protected_simple_arc hW hWconn ha ⟨haR, havoid ha haR⟩
    hb ⟨hbR, havoid hb hbR⟩ hab

end PoincareConjecture.M76
