import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import PoincareConjecture.Proofs.M76.Mathlib.RelativePolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Affine.Mathlib.ContinuousAffineSelection



set_option autoImplicit false
open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]



theorem FinitePiecewiseAffineOn.closed_paste_on_carrier
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsClosed C)
    {old f g : E → (ι → ℝ)}
    (hold : FinitePiecewiseAffineOn old K.space)
    (hf : FinitePiecewiseAffineOn f C) (hg : ContinuousOn g K.space)
    (hgin : EqOn g f (K.space ∩ C))
    (hgout : EqOn g old (K.space \ C)) :
    FinitePiecewiseAffineOn g K.space := by
  obtain ⟨v, W, _, hCW, hv, hvf⟩ := hf.exists_locallyPiecewiseAffine_extension
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  have hlocal : ∃ (J : SimplicialComplex ℝ E) (V : Set K.space),
      J.faces.Finite ∧ IsOpen V ∧ x ∈ V ∧
      Subtype.val '' V ⊆ J.space ∧ FinitePiecewiseAffineOn g J.space := by
    by_cases hx : (x : E) ∈ C
    · obtain ⟨L, hL, hxL, _, hvL⟩ := hv x (hCW hx)
      obtain ⟨J, V, hJ, hJK, hV, hxV, hVJ, hJL⟩ :=
        K.exists_relative_polyhedral_neighborhood hK x
          (isOpen_interior.preimage continuous_subtype_val) hxL
      have hJL' : J.space ⊆ L.space := fun y hy =>
        interior_subset (hJL (show (⟨y, hJK hy⟩ : K.space) ∈
          (Subtype.val : K.space → E) ⁻¹' J.space from hy))
      refine ⟨J, V, hJ, hV, hxV, hVJ, ?_⟩
      apply (hold.restrict J hJ hJK).continuous_selection_pi
        ((hvL.finitePiecewiseAffineOn hL).restrict J hJ hJL') (hg.mono hJK)
      intro y hy
      by_cases hyC : y ∈ C
      · exact Or.inr ((hgin ⟨hJK hy, hyC⟩).trans (hvf hyC).symm)
      · exact Or.inl (hgout ⟨hJK hy, hyC⟩)
    · obtain ⟨J, V, hJ, hJK, hV, hxV, hVJ, hJC⟩ :=
        K.exists_relative_polyhedral_neighborhood hK x
          (hC.isOpen_compl.preimage continuous_subtype_val) hx
      refine ⟨J, V, hJ, hV, hxV, hVJ, (hold.restrict J hJ hJK).congr ?_⟩
      intro y hy
      exact (hgout ⟨hJK hy, hJC (show (⟨y, hJK hy⟩ : K.space) ∈
        (Subtype.val : K.space → E) ⁻¹' J.space from hy)⟩).symm
  obtain ⟨J, V, _, hV, hxV, hVJ, L, hL, hLJ, hgL⟩ := hlocal
  exact ⟨L, V, hL, hV, hxV, fun y hy => hLJ.symm ▸ hVJ hy, hgL⟩

end Geometry
