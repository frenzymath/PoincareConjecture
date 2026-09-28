import PoincareConjecture.Proofs.M76.Mathlib.InnermostPolygonDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Geometry
namespace Set

theorem IsFinitePLBallPair.exists_innermost_polygon_disk
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] [Nonempty ι]
    {D R : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D R)
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinj : ∀ i, Function.Injective (P i))
    (hsub : ∀ i, (P i).boundary ℝ ⊆ D \ R)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) :
    ∃ (i : ι) (d : Set E), IsFinitePLBallPair (ℝ × ℝ) d ((P i).boundary ℝ) ∧
      d ⊆ D \ R ∧ d ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ := by
  classical
  obtain ⟨hRD, C, hC, hcv, hne, e, he, hboundary⟩ := hD
  have hecopy := he
  obtain ⟨f, hf, hef⟩ := hecopy
  obtain ⟨g, hg, heg⟩ := he.symm
  have hgf : LeftInvOn g f D := by
    intro x hx
    rw [← hef ⟨x, hx⟩, ← heg, e.symm_apply_apply]
  have hfg : LeftInvOn f g C := by
    intro x hx
    rw [← heg ⟨x, hx⟩, ← hef, e.apply_symm_apply]
  have hfint {x : E} (hx : x ∈ D \ R) : f x ∈ interior C := by
    rw [← hef ⟨x, hx.1⟩]
    by_contra hn
    exact hx.2 ((hboundary ⟨x, hx.1⟩).mpr ⟨subset_closure (e ⟨x, hx.1⟩).property, hn⟩)
  have hgint {x : ℝ × ℝ} (hx : x ∈ interior C) : g x ∈ D \ R := by
    rw [← heg ⟨x, interior_subset hx⟩]
    refine ⟨(e.symm ⟨x, interior_subset hx⟩).property, ?_⟩
    intro hr
    have hh := (hboundary (e.symm ⟨x, interior_subset hx⟩)).mp hr
    rw [e.apply_symm_apply] at hh
    exact hh.2 hx
  choose m Q hQi hQ hQB using fun i =>
    (P i).exists_polygon_finitePL_image (hP i) (hinj i) hf
      ((hsub i).trans sdiff_subset) (hgf.injOn.mono ((hsub i).trans sdiff_subset))
  have hQsub (i) : (Q i).boundary ℝ ⊆ interior C := by
    rw [hQB i]
    rintro _ ⟨x, hx, rfl⟩
    exact hfint (hsub i hx)
  have hQdis : Pairwise fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ) := by
    intro i j hij
    rw [hQB i, hQB j]
    exact (hdis hij).image hgf.injOn ((hsub i).trans sdiff_subset)
      ((hsub j).trans sdiff_subset)
  obtain ⟨i, hball, hinter, _⟩ := Polygon.exists_innermost_finitePL_disk m Q hQ hQi hQdis
  have hdC : closure (Q i).inside ⊆ interior C :=
    (Q i).closure_inside_subset_convex (hQ i) (hQi i) hcv.interior
      (by rintro _ ⟨v, rfl⟩; exact hQsub i (mem_iUnion.mpr ⟨v, left_mem_affineSegment ℝ _ _⟩))
  have hback (j) : g '' (Q j).boundary ℝ = (P j).boundary ℝ := by
    rw [hQB j, image_image]
    exact (image_congr (hgf.mono ((hsub j).trans sdiff_subset))).trans (image_id _)
  have hd := hball.image_of_subset hg (hdC.trans interior_subset) hfg.injOn
  rw [hback i] at hd
  refine ⟨i, g '' closure (Q i).inside, hd, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hgint (hdC hx)
  · apply Subset.antisymm
    · rintro x ⟨⟨y, hy, hyx⟩, hx⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      have hfy : f x = y := by rw [← hyx, hfg (interior_subset (hdC hy))]
      have hqj : y ∈ (Q j).boundary ℝ :=
        hfy ▸ (hQB j).symm.subset (mem_image_of_mem f hxj)
      have hyi := hinter.subset ⟨hy, mem_iUnion.mpr ⟨j, hqj⟩⟩
      exact (hback i).subset ⟨y, hyi, hyx⟩
    · intro x hx
      exact ⟨hd.1 hx, mem_iUnion.mpr ⟨i, hx⟩⟩

end Set
