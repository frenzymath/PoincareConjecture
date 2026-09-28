import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Counting.CornerVertexComponents









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

theorem exists_original_triangle_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3) :
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] (ℝ × ℝ)),
      Function.LeftInverse R F ∧
      EqOn (F ∘ R) id (convexHull ℝ (s : Set E)) ∧
      F '' base = convexHull ℝ (s : Set E) ∧
      F '' vertices = (s : Set E) ∧
      F '' frontier base = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨v0, v1, v2, h01, h02, h12, hv⟩ := Finset.card_eq_three.mp hs3
  obtain ⟨F, R, hRF, hFR, hF0, hF1, hF2, hFface, _, _, _⟩ :=
    K.exists_returning_face_coordinates h01 h02 h12 (hv ▸ hs)
  have hface : F '' base = convexHull ℝ (s : Set E) := by
    simpa only [base_eq_triangle, hv, Finset.coe_insert, Finset.coe_singleton] using hFface
  have hverts : F '' vertices = (s : Set E) := by
    simp only [vertices, image_insert_eq, image_singleton, hF0, hF1, hF2, hv,
      Finset.coe_insert, Finset.coe_singleton]
  have hfront : F '' frontier base = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hybase := isFinitePLBallPair_base.1 hy
      have hFx := hface.subset (mem_image_of_mem F hybase)
      apply (affine_triangle_frontier_coordinates F R hRF
        (by simpa only [base_eq_triangle] using hface) hFx).mp
      simpa only [hRF y, ← base_eq_triangle] using hy
    · intro hx
      have hxT : x ∈ convexHull ℝ (s : Set E) :=
        intrinsicFrontier_subset (s.finite_toSet.isCompact_convexHull ℝ).isClosed hx
      obtain ⟨y, hy, rfl⟩ := hface.symm.subset hxT
      refine ⟨y, ?_, rfl⟩
      have hh := (affine_triangle_frontier_coordinates F R hRF
        (by simpa only [base_eq_triangle] using hface)
        (hface.subset (mem_image_of_mem F hy))).mpr hx
      simpa only [hRF y, ← base_eq_triangle] using hh
  refine ⟨F, R, hRF, ?_, hface, hverts, hfront⟩
  intro x hx
  apply hFR
  apply convexHull_subset_affineSpan
  simpa only [hv, Finset.coe_insert, Finset.coe_singleton] using hx

theorem normalization_image_component
    {E : Type*} [TopologicalSpace E]
    {F : (ℝ × ℝ) → E} {R : E → ℝ × ℝ}
    (hF : Continuous F) (hR : Continuous R) (hRF : Function.LeftInverse R F)
    {T : Set (ℝ × ℝ)} {x : ℝ × ℝ} (hx : x ∈ T) :
    F '' connectedComponentIn T x = connectedComponentIn (F '' T) (F x) := by
  apply Subset.antisymm (hF.continuousOn.image_connectedComponentIn_subset hx)
  intro y hy
  have hRy := hR.continuousOn.image_connectedComponentIn_subset (mem_image_of_mem F hx)
    (mem_image_of_mem R hy)
  have hRT : R '' (F '' T) = T := by
    rw [image_image]
    exact (image_congr fun z _ => hRF z).trans (image_id T)
  rw [hRT, hRF x] at hRy
  obtain ⟨z, hz, rfl⟩ := connectedComponentIn_subset _ _ hy
  exact ⟨z, hRF z ▸ hRy, rfl⟩

end PoincareConjecture.M76.TriangleCorner
