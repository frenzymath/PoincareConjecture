import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.PlanarStarIncidence
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.LineStarCircles
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FullSubcomplexStars
import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates

set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

local notation "V2" => (Fin 2 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in
theorem boundary_real_stars_of_marked_planar_halfspace_stars
    (K B : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hBK : B ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ B.vertices) → s ∈ B.faces)
    (hstars : ∀ p ∈ K.vertices, ∃ (a : E → V2) (V : Set V2),
      (K.closedStar p).AffineOnFaces a ∧ InjOn a (K.closedStar p).space ∧
      IsOpen V ∧ a p ∈ V ∧
      ((V ⊆ a '' (K.closedStar p).space ∧ Disjoint (K.closedStar p).space B.space) ∨
        ∃ (ell : V2 →ᴬ[ℝ] ℝ) (v : V2), ell.contLinear v = 1 ∧
          V ∩ {z | 0 ≤ ell z} ⊆ a '' (K.closedStar p).space ∧
          a '' (K.closedStar p).space ⊆ {z | 0 ≤ ell z} ∧
          ∀ x ∈ (K.closedStar p).space, x ∈ B.space ↔ ell (a x) = 0)) :
    ∀ p ∈ B.vertices, ∃ (b : E → ℝ),
      (B.closedStar p).AffineOnFaces b ∧ InjOn b (B.closedStar p).space ∧
      b p ∈ interior (b '' (B.closedStar p).space) := by
  classical
  intro p hpB
  have hpK : p ∈ K.vertices := hBK hpB
  have hpface : {p} ∈ K.faces := hpK
  have hpstar : p ∈ (K.closedStar p).space :=
    (K.closedStar p).subset_space
      (show {p} ∈ (K.closedStar p).faces from ⟨hpface, by simpa using hpface⟩)
      (Finset.mem_singleton_self p)
  have hstar := K.closedStar_space_eq_inter_of_full B hK hBK hfull hpB
  have hsub : (B.closedStar p).space ⊆ (K.closedStar p).space := by
    rw [hstar]
    exact inter_subset_left
  have hmarksub : (B.closedStar p).space ⊆ B.space := by
    rw [hstar]
    exact inter_subset_right
  obtain ⟨a, V, hf, hinj, hV, hpV, hcase⟩ := hstars p hpK
  rcases hcase with ⟨_, hdis⟩ | ⟨ell, v, hv, hpatch, _, hmark⟩
  · exact False.elim (disjoint_left.mp hdis hpstar (B.vertices_subset_space hpB))
  · have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have he : ell.toAffineMap.linear v = 1 := hv
      rw [h, LinearMap.zero_apply] at he
      exact zero_ne_one he
    obtain ⟨l, r, hrl, hlr, hlzero⟩ := ell.toAffineMap.exists_zeroLevel_coordinates
      (F := ℝ) hell (by simp)
    have hzero (x : E) (hx : x ∈ (B.closedStar p).space) : ell (a x) = 0 :=
      (hmark x (hsub hx)).mp (hmarksub hx)
    have hpzero : ell (a p) = 0 := (hmark p hpstar).mp (B.vertices_subset_space hpB)
    have hfB : (B.closedStar p).AffineOnFaces a :=
      fun s hs => hf s ⟨hBK hs.1, hBK hs.2⟩
    refine ⟨r ∘ a, hfB.postcomp r, ?_, ?_⟩
    · intro x hx y hy hxy
      apply hinj (hsub hx) (hsub hy)
      have h := congrArg l hxy
      exact (hlr (hzero x hx)).symm.trans (h.trans (hlr (hzero y hy)))
    · have hnear : l ⁻¹' V ⊆ (r ∘ a) '' (B.closedStar p).space := by
        intro t ht
        obtain ⟨x, hx, hax⟩ := hpatch ⟨ht, (show ell (l t) = 0 from hlzero t).ge⟩
        have hxB : x ∈ B.space := (hmark x hx).mpr (by rw [hax]; exact hlzero t)
        refine ⟨x, hstar.symm.subset ⟨hx, hxB⟩, ?_⟩
        change r (a x) = t
        rw [hax, hrl]
      apply interior_maximal hnear (hV.preimage l.continuous)
      change l (r (a p)) ∈ V
      rw [hlr hpzero]
      exact hpV

theorem hasDisjointPolygonPresentation_boundary_of_marked_planar_halfspace_stars
    (K B : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hBK : B ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ B.vertices) → s ∈ B.faces)
    (hstars : ∀ p ∈ K.vertices, ∃ (a : E → V2) (V : Set V2),
      (K.closedStar p).AffineOnFaces a ∧ InjOn a (K.closedStar p).space ∧
      IsOpen V ∧ a p ∈ V ∧
      ((V ⊆ a '' (K.closedStar p).space ∧ Disjoint (K.closedStar p).space B.space) ∨
        ∃ (ell : V2 →ᴬ[ℝ] ℝ) (v : V2), ell.contLinear v = 1 ∧
          V ∩ {z | 0 ≤ ell z} ⊆ a '' (K.closedStar p).space ∧
          a '' (K.closedStar p).space ⊆ {z | 0 ≤ ell z} ∧
          ∀ x ∈ (K.closedStar p).space, x ∈ B.space ↔ ell (a x) = 0)) :
    HasDisjointPolygonPresentation B.space :=
  B.hasDisjointPolygonPresentation_of_real_stars (hK.subset hBK)
    (K.boundary_real_stars_of_marked_planar_halfspace_stars B hK hBK hfull hstars)

end Geometry.SimplicialComplex
