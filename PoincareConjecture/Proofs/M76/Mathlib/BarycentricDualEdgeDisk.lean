import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualLink
import PoincareConjecture.Proofs.M76.Mathlib.InteriorEdgeLinkPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonClosedStarDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

omit [DecidableEq E] in

theorem faceCentroid_mem_barycentricDualBlock_vertices
    {s : Finset E} (hs : s ∈ K.faces) :
    s.centroid ℝ id ∈ (K.barycentricDualBlock s).vertices := by
  refine ⟨(K.mem_barycentricSubdivision_vertices_iff _).mpr ⟨s, hs, rfl⟩, ?_⟩
  intro x hx
  have hx' := Finset.mem_singleton.mp hx
  exact ⟨s, hs, Subset.rfl, hx'.symm⟩

theorem barycentricDualBlock_closedStar_faceCentroid
    {s : Finset E} (hs : s ∈ K.faces) :
    (K.barycentricDualBlock s).closedStar (s.centroid ℝ id) =
      K.barycentricDualBlock s := by
  classical
  ext f
  constructor
  · exact fun hf => hf.1
  · intro hf
    obtain ⟨a, ha, hchain, hfa⟩ := (K.barycentricSubdivision_faces f).mp hf.1
    have hcoface (i : K.faces) (hi : i ∈ a) : s ⊆ i.val := by
      obtain ⟨t, ht, hst, hti⟩ := hf.2 _
        (hfa.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have he' : (⟨t, ht⟩ : K.faces) = i := K.faceCentroid_injective hti
      exact congrArg Subtype.val he' ▸ hst
    refine ⟨hf, ⟨?_, ?_⟩⟩
    · apply (K.barycentricSubdivision_faces _).mpr
      refine ⟨insert ⟨s, hs⟩ a, Finset.insert_nonempty _ _, ?_, ?_⟩
      · intro i hi j hj
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Or.inl le_rfl
          · exact Or.inl (hcoface j hj)
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Or.inr (hcoface i hi)
          · exact hchain i hi j hj
      · rw [Finset.image_insert, ← hfa]
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨s, hs, Subset.rfl, rfl⟩
      · exact hf.2 x hx

variable [FiniteDimensional ℝ E]

theorem isFinitePLBallPair_barycentricDualBlock_of_interior_edge
    (h3 : Module.finrank ℝ E = 3) {s : Finset E}
    (hs : s ∈ K.faces) (hscard : s.card = 2)
    (hmeet : (convexHull ℝ (s : Set E) ∩ interior K.space).Nonempty) :
    IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock s).space
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
  obtain ⟨n, P, hPi, hP, hPs⟩ := K.exists_polygon_faceLink_of_interior_edge
    (Set.toFinite K.faces) h3 hs hscard hmeet
  obtain ⟨_, e, ⟨g, hg, heg⟩, _, _⟩ := K.exists_finitePL_barycentricDualLink hs
  have hginj : InjOn g (K.faceLink s).space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [heg] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  have hgs : g '' (K.faceLink s).space =
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← heg ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← heg, e.apply_symm_apply]
  obtain ⟨m, Q, hQi, hQ, hQb⟩ := P.exists_polygon_finitePL_image hP hPi hg
    hPs.subset (hginj.mono hPs.subset)
  have hQs : Q.boundary ℝ =
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
    rw [hQb, hPs, hgs]
  have hball := (K.barycentricDualBlock s).isFinitePLBallPair_closedStar_of_polygon_link
    (K.barycentricDualBlock_finite s) (K.faceCentroid_mem_barycentricDualBlock_vertices hs)
    Q hQ hQi hQs
  simpa only [K.barycentricDualBlock_closedStar_faceCentroid hs] using hball

end Geometry.SimplicialComplex
