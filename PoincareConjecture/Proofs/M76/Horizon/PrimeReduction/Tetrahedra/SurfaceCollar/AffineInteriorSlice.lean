import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.ConvexPlanarBoundaryPush









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_interior_zero_of_affine_crossing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) (hne : (interior C).Nonempty)
    (A : E →ᵃ[ℝ] ℝ) {p q : E} (hp : p ∈ C) (hq : q ∈ C)
    (hpA : A p < 0) (hqA : 0 < A q) :
    ∃ w ∈ interior C, A w = 0 := by
  obtain ⟨w,hw⟩ := hne
  rcases lt_trichotomy (A w) 0 with hn | hz | hpos
  · let t := -A w / (A q - A w)
    have hden : 0 < A q - A w := by linarith
    have ht : t ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (neg_pos.mpr hn) hden
      · exact (div_lt_one hden).mpr (by linarith)
    refine ⟨AffineMap.lineMap w q t,
      hC.openSegment_interior_self_subset_interior hw hq
        (by rw [openSegment_eq_image_lineMap]; exact mem_image_of_mem _ ht),?_⟩
    rw [AffineMap.apply_lineMap,AffineMap.lineMap_apply_ring]
    dsimp [t]
    field_simp
    ring
  · exact ⟨w,hw,hz⟩
  · let t := A w / (A w - A p)
    have hden : 0 < A w - A p := by linarith
    have ht : t ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos hpos hden
      · exact (div_lt_one hden).mpr (by linarith)
    refine ⟨AffineMap.lineMap w p t,
      hC.openSegment_interior_self_subset_interior hw hp
        (by rw [openSegment_eq_image_lineMap]; exact mem_image_of_mem _ ht),?_⟩
    rw [AffineMap.apply_lineMap,AffineMap.lineMap_apply_ring]
    dsimp [t]
    field_simp
    ring

theorem exists_supported_convex_plane_push_of_crossing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C U : Set E} (hC : Convex ℝ C) (hne : (interior C).Nonempty)
    (hU : IsOpen U) {y p q : E} (hy : y ∈ C) (hyU : y ∈ U)
    (A : E →ᵃ[ℝ] ℝ) (hyA : A y = 0)
    (hp : p ∈ C) (hq : q ∈ C) (hpA : A p < 0) (hqA : 0 < A q) :
    ∃ H : E ≃ₜ E,
      (∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn (H : E → E) K.space) ∧
      (∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn (H.symm : E → E) K.space) ∧
      EqOn H id Uᶜ ∧ (∀ x, A (H x) = A x) ∧
      (∀ x ∈ C, H x ∈ interior C ∨ H x = x) ∧ H y ∈ interior C := by
  obtain ⟨w,hw,hwA⟩ := exists_interior_zero_of_affine_crossing hC hne A hp hq hpA hqA
  exact exists_supported_convex_plane_push hC hU hy hyU hw A (hwA.trans hyA.symm)

end PoincareConjecture.M76
