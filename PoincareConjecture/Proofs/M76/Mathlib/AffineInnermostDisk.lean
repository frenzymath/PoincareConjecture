import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.InnermostPolygonDisk

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_innermost_affine_disk {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → ℕ) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinj : ∀ i, Function.Injective (P i))
    (hdisj : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    (a : (ℝ × ℝ) →ᴬ[ℝ] E) (ha : Function.Injective a) (S : Set E)
    (hsection : a ⁻¹' S = ⋃ i, (P i).boundary ℝ) :
    ∃ i, IsFinitePLBallPair (ℝ × ℝ) (a '' closure (P i).inside)
        (a '' (P i).boundary ℝ) ∧
      (a '' closure (P i).inside) ∩ S = a '' (P i).boundary ℝ ∧
      Disjoint (a '' (P i).inside) S := by
  obtain ⟨i, hdisk, hinter, hmiss⟩ := exists_innermost_finitePL_disk n P hP hinj hdisj
  refine ⟨i, hdisk.affine_image a ha.injOn, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxS⟩
      exact ⟨x, hinter ▸ (show x ∈ closure (P i).inside ∩ ⋃ j, (P j).boundary ℝ from
        ⟨hx, hsection ▸ hxS⟩), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨x, hdisk.1 hx, rfl⟩, ?_⟩
      change x ∈ a ⁻¹' S
      rw [hsection]
      exact mem_iUnion.mpr ⟨i, hx⟩
  · apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxS
    exact Set.disjoint_left.mp hmiss hx (hsection ▸ hxS)

end Polygon
