import PoincareConjecture.Proofs.M76.Mathlib.LocalPLHalfspaceGluing
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd










set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem LocallyPiecewiseAffineOn.affine_halfspace_paste
    {f g : E → F} {U : Set E} (hf : LocallyPiecewiseAffineOn f U)
    (hg : LocallyPiecewiseAffineOn g U) (a : E →ᵃ[ℝ] ℝ)
    (hagree : ∀ x ∈ U, a x = 0 → f x = g x) :
    LocallyPiecewiseAffineOn (fun x => if 0 ≤ a x then f x else g x) U := by
  classical
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  obtain ⟨L, hL, hxL, _, hgL⟩ := hg x hx
  obtain ⟨R, hR, hxR, hRKL⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed isCompact_singleton
      (isOpen_interior.inter isOpen_interior) (singleton_subset_iff.mpr ⟨hxK, hxL⟩)
  have hRU : R.space ⊆ U := fun y hy => hKU (interior_subset (hRKL hy).1)
  have hfR := (hfK.finitePiecewiseAffineOn hK).restrict R hR
    (fun _ hy => interior_subset (hRKL hy).1)
  have hgR := (hgL.finitePiecewiseAffineOn hL).restrict R hR
    (fun _ hy => interior_subset (hRKL hy).2)
  let h : E → F := fun y => if 0 ≤ a y then f y else g y
  have hpos : FinitePiecewiseAffineOn h (R.space ∩ {y | 0 ≤ a y}) := by
    obtain ⟨T, hT, hTs⟩ := R.exists_finite_triangulation_inter_halfspaces hR {-a}
    have hhalf : {y | ∀ b ∈ ({-a} : Finset (E →ᵃ[ℝ] ℝ)), b y ≤ 0} =
        {y | 0 ≤ a y} := by
      ext y
      simp only [Finset.mem_singleton, forall_eq, AffineMap.coe_neg, Pi.neg_apply,
        neg_nonpos]
    rw [hhalf] at hTs
    have hfT := hfR.restrict T hT (hTs.subset.trans inter_subset_left)
    rw [hTs] at hfT
    exact hfT.congr (fun y hy => (if_pos hy.2).symm)
  have hneg : FinitePiecewiseAffineOn h (R.space ∩ {y | a y ≤ 0}) := by
    obtain ⟨T, hT, hTs⟩ := R.exists_finite_triangulation_inter_halfspaces hR {a}
    have hhalf : {y | ∀ b ∈ ({a} : Finset (E →ᵃ[ℝ] ℝ)), b y ≤ 0} =
        {y | a y ≤ 0} := by
      ext y
      simp only [Finset.mem_singleton, forall_eq]
    rw [hhalf] at hTs
    have hgT := hgR.restrict T hT (hTs.subset.trans inter_subset_left)
    rw [hTs] at hgT
    apply hgT.congr
    intro y hy
    by_cases hay : 0 ≤ a y
    · simpa only [h, if_pos hay] using (hagree y (hRU hy.1) (hy.2.antisymm hay)).symm
    · simp only [h, if_neg hay]
  have hcover : (R.space ∩ {y | 0 ≤ a y}) ∪
      (R.space ∩ {y | a y ≤ 0}) = R.space := by
    ext y
    constructor
    · rintro (hy | hy) <;> exact hy.1
    · intro hy
      rcases le_total 0 (a y) with ha | ha
      · exact Or.inl ⟨hy, ha⟩
      · exact Or.inr ⟨hy, ha⟩
  have htotal := finitePiecewiseAffineOn_union hpos hneg
  rw [hcover] at htotal
  obtain ⟨T, hT, hTs, hmap⟩ := htotal
  exact ⟨T, hT, hTs.symm ▸ hxR (mem_singleton x), hTs.subset.trans hRU, hmap⟩

end Geometry
