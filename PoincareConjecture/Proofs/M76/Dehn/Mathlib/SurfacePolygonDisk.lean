import PoincareConjecture.Proofs.M76.Mathlib.ConvexFiniteAffineCover
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.PLSpherePolygonCut
import PoincareConjecture.Proofs.M76.Mathlib.TriangularHalfBalls

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E)

theorem exists_point_outside_polygon_of_pure
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    {n : ℕ} (P : Polygon E (n + 3)) (hPK : P.boundary ℝ ⊆ K.space) :
    ∃ p : K.space, (p : E) ∉ P.boundary ℝ := by
  classical
  obtain ⟨s, hs, _⟩ := mem_space_iff.mp (hPK (P.vertex_mem_boundary 0))
  obtain ⟨t, ht, _, hcard⟩ := hpure s hs
  by_contra h
  have hsub : K.space ⊆ P.boundary ℝ := by
    intro x hx
    by_contra hn
    exact h ⟨⟨x, hx⟩, hn⟩
  have hcover : convexHull ℝ (t : Set E) ⊆
      ⋃ i : Fin (n + 3), (affineSpan ℝ (P.edgeVertices i : Set E) : Set E) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub (K.convexHull_subset_space ht hx))
    refine mem_iUnion.mpr ⟨i, convexHull_subset_affineSpan _ ?_⟩
    rwa [P.edgeSet_eq_convexHull] at hi
  have hne : (convexHull ℝ (t : Set E)).Nonempty :=
    (K.nonempty_of_mem_faces ht).to_set.mono (subset_convexHull ℝ _)
  obtain ⟨i, hi⟩ :=
    (convex_convexHull ℝ (t : Set E)).exists_subset_affineSubspace_of_subset_iUnion hne
      (fun i : Fin (n + 3) => affineSpan ℝ (P.edgeVertices i : Set E)) hcover
  have hle := (K.indep ht).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans hi)
  have htwo : (P.edgeVertices i).card ≤ 2 := by
    calc
      (P.edgeVertices i).card ≤ ({P (finRotate (n + 3) i)} : Finset E).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  omega

theorem exists_roof_sphere_polygon_disks
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (e : K.space ≃ₜ frontier (TriangularRoofModel.halfBall 1)) (he : e.IsFinitePL)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hPK : P.boundary ℝ ⊆ K.space) :
    ∃ b c : Set E, IsFinitePLBallPair (ℝ × ℝ) b (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) c (P.boundary ℝ) ∧ b ∪ c = K.space ∧
      b ∩ c = P.boundary ℝ := by
  obtain ⟨p, hp⟩ := K.exists_point_outside_polygon_of_pure hpure P hPK
  have hcv : Convex ℝ (TriangularRoofModel.halfBall 1) := by
    rw [TriangularRoofModel.halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage
      (TriangularRoofModel.halfBallForms 1 i)
  obtain ⟨b, c, hb, hc, hu, hi, _⟩ := he.exists_polygon_cut
    (TriangularRoofModel.isCompact_halfBall (Or.inl rfl)) hcv
    (TriangularRoofModel.interior_halfBall_nonempty (Or.inl rfl))
    (by simp [Module.finrank_prod]) P hP hinj hPK p hp
  exact ⟨b, c, hb, hc, hu, hi⟩

end Geometry.SimplicialComplex
