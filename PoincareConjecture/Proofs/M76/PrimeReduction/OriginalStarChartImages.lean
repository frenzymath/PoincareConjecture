import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X]




theorem exists_original_closedStar_image_neighborhood
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ K.vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    InjOn (fun z => B (g z)) (K.closedStar p).space ∧
      ∃ V : Set V3, IsOpen V ∧ B (g p) ∈ V ∧
        (V ⊆ (fun z => B (g z)) '' (K.closedStar p).space ∨
          ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
            V ∩ {z | 0 ≤ ell z} ⊆ (fun z => B (g z)) '' (K.closedStar p).space ∧
            (fun z => B (g z)) '' (K.closedStar p).space ⊆ {z | 0 ≤ ell z} ∧
            ∀ z ∈ (K.closedStar p).space,
              (g z : X) ∈ frontier R ↔ ell (B (g z)) = 0) := by
  obtain ⟨hinj, O, hO, hpO, hOB, hOR⟩ :=
    K.exists_original_open_neighborhood_of_closedStar hK H g hg hp B hsource
  refine ⟨hinj, B '' O, B.isOpen_image_of_subset_source hO hOB,
    mem_image_of_mem B hpO, ?_⟩
  rcases hregion with hinterior | ⟨ell, v, hv, hhalf⟩
  · left
    rintro z ⟨x, hxO, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hOR ⟨hxO, hinterior (hOB hxO)⟩
    exact ⟨y, hy, congrArg B hyx⟩
  · right
    refine ⟨ell, v, hv, ?_, ?_, ?_⟩
    · rintro z ⟨⟨x, hxO, rfl⟩, hxell⟩
      obtain ⟨y, hy, hyx⟩ := hOR ⟨hxO, (hhalf x (hOB hxO)).mpr hxell⟩
      exact ⟨y, hy, congrArg B hyx⟩
    · rintro z ⟨x, hx, rfl⟩
      exact (hhalf (g x) (hsource hx)).mp (g x).property
    · have hlin : ell.toAffineMap.linear ≠ 0 := by
        intro h
        have hval : ell.toAffineMap.linear v = 1 := hv
        rw [h] at hval
        exact zero_ne_one hval
      intro z hz
      exact ((B.isImage_frontier_of_affine_nonneg ell hlin hhalf).apply_mem_iff
        (hsource hz)).symm

end PoincareConjecture.M76
