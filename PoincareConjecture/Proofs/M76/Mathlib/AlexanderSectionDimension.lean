import PoincareConjecture.Proofs.M76.Mathlib.ConvexFiniteAffineCover
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityPresentation

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem HasAlexanderCurvePresentation.card_le_two_of_convexHull_subset
    {S : Set E} {a : ℕ} (h : HasAlexanderCurvePresentation S a)
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    (hsub : convexHull ℝ (s : Set E) ⊆ S) : s.card ≤ 2 := by
  classical
  obtain rfl | hsne := s.eq_empty_or_nonempty
  · simp
  obtain ⟨m, n, P, r, _, hr, hcover, _, _⟩ := h
  let : Finite r := hr.finite.to_subtype
  let I := r ⊕ (Σ i : Fin m, Fin (n i + 3))
  let v : I → Finset E := fun i => match i with
    | Sum.inl x => {x.val}
    | Sum.inr ij => {P ij.1 ij.2, P ij.1 (finRotate (n ij.1 + 3) ij.2)}
  have hv (i : I) : (v i).card ≤ 2 := by
    rcases i with x | ⟨i, j⟩
    · simp [v]
    · calc
        (v (Sum.inr ⟨i, j⟩)).card ≤
            ({P i (finRotate (n i + 3) j)} : Finset E).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp
  have hlineCover : S ⊆ ⋃ i : I, (affineSpan ℝ (v i : Set E) : Set E) := by
    intro x hx
    rcases hcover.subset hx with hxr | hxP
    · exact mem_iUnion.mpr ⟨Sum.inl ⟨x, hxr⟩,
        subset_affineSpan ℝ _ (by simp [v])⟩
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxP
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxi
      have heq : convexHull ℝ (v (Sum.inr ⟨i, j⟩) : Set E) = (P i).edgeSet ℝ j := by
        simp only [v, Finset.coe_pair, convexHull_pair, Polygon.edgeSet,
          affineSegment_eq_segment]
      exact mem_iUnion.mpr ⟨Sum.inr ⟨i, j⟩,
        convexHull_subset_affineSpan _ (heq.symm ▸ hxj)⟩
  have hne : (convexHull ℝ (s : Set E)).Nonempty :=
    hsne.to_set.mono (subset_convexHull ℝ _)
  have hcv := convex_convexHull ℝ (s : Set E)
  obtain ⟨i, hi⟩ := hcv.exists_subset_affineSubspace_of_subset_iUnion hne
    (fun i : I => affineSpan ℝ (v i : Set E)) (hsub.trans hlineCover)
  exact (hs.card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans hi)).trans (hv i)

end Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_ne_height_on_triangle_of_presentation
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) {c : ℝ} {a : ℕ}
    (hpres : HasAlexanderCurvePresentation (K.space ∩ {x | A x = c}) a)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3) :
    ∃ v ∈ s, A v ≠ c := by
  classical
  by_contra h
  push Not at h
  have hplane : convexHull ℝ (s : Set E) ⊆ {x | A x = c} :=
    convexHull_min (fun x hx => h x hx) ((convex_singleton c).affine_preimage A)
  have hle := hpres.card_le_two_of_convexHull_subset (K.indep hs)
    (fun x hx => ⟨K.convexHull_subset_space hs hx, hplane hx⟩)
  omega

end Geometry.SimplicialComplex
