import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.VertexStarChartRestriction
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X]

theorem exists_original_boundary_star_chart
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K)
    {R : Set X} (g : E → R) (HB : A.space ≃ₜ frontier R)
    (hHB : ∀ z : A.space, (HB z : X) = (g z : X))
    {p : E} (hp : p ∈ A.vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (r : V3 →ᴬ[ℝ] V2) (q : OpenPartialHomeomorph A.space V2),
      (∀ z : A.space, (z : E) ∈ (A.closedStar p).space → z ∈ q.source) ∧
      (∀ z : A.space, q z = r (B (g z))) ∧
      (A.closedStar p).AffineOnFaces (fun z => r (B (g z))) := by
  have hstar : A.closedStar p ≤ K.closedStar p :=
    fun _ hs => ⟨hAK hs.1, hAK hs.2⟩
  have hpA : p ∈ A.space := A.vertices_subset_space hp
  have hpface : {p} ∈ A.faces := hp
  have hpstar : p ∈ (A.closedStar p).space := by
    apply (A.closedStar p).convexHull_subset_space (s := {p})
    · exact ⟨hpface, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
        using hpface⟩
    · simp
  have hpB := hsource (SimplicialComplex.space_subset_of_le hstar hpstar)
  have hpfront : (g p : X) ∈ frontier R := by
    rw [← hHB ⟨p, hpA⟩]
    exact (HB ⟨p, hpA⟩).property
  rcases hregion with hinterior | ⟨ell, v, hv, hhalf⟩
  · exact False.elim (hpfront.2 (interior_maximal hinterior B.open_source hpB))
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    exact zero_ne_one hval
  obtain ⟨a, r, hra, har, haz⟩ :=
    ell.toAffineMap.exists_zeroLevel_coordinates (F := V2) hell (by simp)
  obtain ⟨q0, hqsource, _, hqval, _⟩ := B.exists_affine_hypersurface_chart
    ell (B.isImage_frontier_of_affine_nonneg ell hell hhalf) a r hra har haz (HB ⟨p, hpA⟩)
  let q := HB.toOpenPartialHomeomorph.trans q0
  refine ⟨r, q, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨mem_univ _, ?_⟩
    change HB z ∈ q0.source
    rw [hqsource]
    change (HB z : X) ∈ B.source
    rw [hHB]
    exact hsource (SimplicialComplex.space_subset_of_le hstar hz)
  · intro z
    change q0 (HB z) = r (B (g z))
    rw [hqval, hHB]
  · exact (show (A.closedStar p).AffineOnFaces (fun z => B (g z)) from
      fun s hs => hface s (hstar hs)).postcomp r

theorem original_boundary_faceAffine_vertex_stars
    (K A : SimplicialComplex ℝ E) (hA : A.faces.Finite) (hAK : A ≤ K)
    {R : Set X} (g : E → R) (HB : A.space ≃ₜ frontier R)
    (hHB : ∀ z : A.space, (HB z : X) = (g z : X))
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) :
    ∀ p : E, {p} ∈ A.faces → ∃ f : E → V2,
      (A.closedFaceStar {p}).AffineOnFaces f ∧
      InjOn f (A.closedFaceStar {p}).space ∧
      f p ∈ interior (f '' (A.closedFaceStar {p}).space) := by
  intro p hp
  obtain ⟨B, hsource, hface, hregion⟩ := hstars p (hAK hp)
  obtain ⟨r, q, hqsource, hqval, hqface⟩ :=
    exists_original_boundary_star_chart K A hAK g HB hHB hp B hsource hface hregion
  let f : E → V2 := fun z => r (B (g z))
  have hstar : A.closedFaceStar {p} = A.closedStar p :=
    A.closedFaceStar_singleton_eq_closedStar p
  refine ⟨f, hstar.symm ▸ hqface, ?_⟩
  exact A.injOn_and_interior_closedStar_of_chart hA hp q f
    (fun z hz => hqsource z (hstar ▸ hz)) (fun z _ => hqval z)

end PoincareConjecture.M76
