import PoincareConjecture.Proofs.M76.Mathlib.FinitePLClosedExtension
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood

set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem locallyPiecewiseAffineOn_of_halfspace_replacement
    {f g : E → F} {U C S : Set E}
    (hf : LocallyPiecewiseAffineOn f U) (hg : FinitePiecewiseAffineOn g S)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (hC : C = {x | ∀ i, L i x ≤ 1}) (hinside : U ∩ C ⊆ S)
    (hfixed : EqOn g f (U \ interior C)) : LocallyPiecewiseAffineOn g U := by
  classical
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  have hgcopy := hg
  obtain ⟨J, hJ, hJS, _⟩ := hgcopy
  obtain ⟨R, hR, hRs⟩ := K.exists_finite_triangulation_inter J hK hJ
  rw [hJS] at hRs
  have hgin : FinitePiecewiseAffineOn g (K.space ∩ S) := by
    rw [← hRs]
    exact hg.restrict R hR (hRs.subset.trans inter_subset_right)
  have houtside (i : ι) (y : E) (hy : 1 ≤ L i y) : y ∉ interior C := by
    by_cases hyC : y ∈ C
    · have hbound : ∀ j, L j y ≤ 1 := by
        have hm : y ∈ {z | ∀ j, L j z ≤ 1} := hC ▸ hyC
        exact hm
      have hyfront : y ∈ frontier C := by
        rw [hC, frontier_finite_linear_unit_halfspaces L hL]
        exact ⟨hbound, i, (hbound i).antisymm hy⟩
      exact hyfront.2
    · exact fun h => hyC (interior_subset h)
  have hpieces (i : ι) :
      FinitePiecewiseAffineOn g (K.space ∩ {y | 1 ≤ L i y}) := by
    let A : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E 1 - (L i).toAffineMap
    obtain ⟨T, hT, hTs⟩ := K.exists_finite_triangulation_inter_halfspaces hK {A}
    have hTA : {y | ∀ a ∈ ({A} : Finset (E →ᵃ[ℝ] ℝ)), a y ≤ 0} =
        {y | 1 ≤ L i y} := by
      ext y
      simp only [Finset.mem_singleton, forall_eq, A, AffineMap.coe_sub,
        Pi.sub_apply, AffineMap.const_apply, LinearMap.coe_toAffineMap, sub_nonpos]
    rw [hTA] at hTs
    have hfT := hfK.finitePiecewiseAffineOn hK |>.restrict T hT
      (hTs.subset.trans inter_subset_left)
    rw [hTs] at hfT
    exact hfT.congr (fun y hy => (hfixed ⟨hKU hy.1, houtside i y hy.2⟩).symm)
  have hcover : (K.space ∩ S) ∪ (⋃ i, K.space ∩ {y | 1 ≤ L i y}) = K.space := by
    apply Subset.antisymm
    · rintro y (hy | hy)
      · exact hy.1
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        exact hi.1
    · intro y hy
      by_cases hyC : y ∈ C
      · exact Or.inl ⟨hy, hinside ⟨hKU hy, hyC⟩⟩
      · have hn : ¬ ∀ i, L i y ≤ 1 := fun h => hyC (hC.symm ▸ h)
        push Not at hn
        obtain ⟨i, hi⟩ := hn
        exact Or.inr (mem_iUnion.mpr ⟨i, hy, hi.le⟩)
  have htotal := finitePiecewiseAffineOn_union hgin (FinitePiecewiseAffineOn.iUnion hpieces)
  rw [hcover] at htotal
  obtain ⟨T, hT, hTs, hgT⟩ := htotal
  exact ⟨T, hT, hTs.symm ▸ hxK, hTs.subset.trans hKU, hgT⟩

end Geometry
