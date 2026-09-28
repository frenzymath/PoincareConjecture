import PoincareConjecture.Proofs.M76.Mathlib.InnermostTouchingPolygonDisk
import PoincareConjecture.Proofs.M76.Mathlib.AffinePolygonDiskChart










set_option autoImplicit false

open Set TriangularRoofModel

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_innermost_affine_disk_of_singleton_inter {ι : Type*}
    [Finite ι] [Nonempty ι] (n : ι → ℕ) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinj : ∀ i, Function.Injective (P i))
    (q : ℝ × ℝ)
    (hinter : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    (a : (ℝ × ℝ) →ᴬ[ℝ] E) (ha : Function.Injective a) (S : Set E)
    (hsection : a ⁻¹' S = ⋃ i, (P i).boundary ℝ) :
    ∃ (i : ι) (e : (a '' closure (P i).inside) ≃ₜ disk),
      IsFinitePLBallPair (ℝ × ℝ) (a '' closure (P i).inside) (a '' (P i).boundary ℝ) ∧
      e.IsFinitePL ∧
      (∀ x : a '' closure (P i).inside,
        (x : E) ∈ a '' (P i).boundary ℝ ↔ (e x : (ℝ × ℝ) × ℝ) ∈ rim) ∧
      (a '' closure (P i).inside) ∩ S = a '' (P i).boundary ℝ ∧
      Disjoint (a '' (P i).inside) S := by
  obtain ⟨i, hdisk, hmeet, hmiss⟩ :=
    exists_innermost_finitePL_disk_of_singleton_inter n P hP hinj q hinter
  obtain ⟨e, he, hb⟩ := (P i).exists_affine_disk_chart (hP i) (hinj i) a ha
  refine ⟨i, e, hdisk.affine_image a ha.injOn, he, hb, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxS⟩
      exact ⟨x, hmeet ▸ (show x ∈ closure (P i).inside ∩ ⋃ j, (P j).boundary ℝ from
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
