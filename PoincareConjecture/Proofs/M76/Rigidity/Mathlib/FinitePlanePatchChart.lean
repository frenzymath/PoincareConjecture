import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Mathlib.PrescribedSubdivisionVertices










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne






theorem exists_pair_chart_of_finitePL_plane_patch {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    {Q : Set (ℝ × ℝ)} {S V : Set E} {f : (ℝ × ℝ) → E}
    (hf : FinitePiecewiseAffineOn f Q) (hinj : InjOn f Q)
    (hf0 : f 0 = 0) (h0Q : (0 : ℝ × ℝ) ∈ interior Q)
    (hV : IsOpen V) (h0V : (0 : E) ∈ V)
    (hfull : S ∩ V = (f '' Q) ∩ V) :
    ∃ H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ),
      (0 : E) ∈ H.source ∧ H.source ⊆ V ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧ H 0 = 0 ∧
      ∀ x ∈ H.source, x ∈ S ↔ (H x).2 = 0 := by
  classical
  obtain ⟨K, hK, hKQ, hfK⟩ := hf
  obtain ⟨L, hL, hLK, h0L⟩ := K.exists_finite_subdivision_with_vertices hK {0}
    (by simpa only [Finset.coe_singleton, singleton_subset_iff, hKQ]
        using interior_subset h0Q)
  have hLQ : L.space = Q := hLK.space_eq.trans hKQ
  have h0L' : (0 : ℝ × ℝ) ∈ L.vertices := h0L (by simp)
  have hfL : L.AffineOnFaces f := hLK.affineOnFaces hfK
  have hinjL : InjOn f L.space := hinj.mono hLQ.subset
  have hsource := L.isFinitePLBallPair_closedStar_of_interior hL h0L'
    (hLQ.symm ▸ h0Q) (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  obtain ⟨n, P, hPi, hPe, hPb⟩ := hsource.exists_polygon_boundary
  have hlinksub : (L.link 0).space ⊆ L.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hPQ : P.boundary ℝ ⊆ Q := hPb.subset.trans (hlinksub.trans hLQ.subset)
  obtain ⟨m, P0, hP0i, hP0e, hP0b⟩ :=
    P.exists_polygon_finitePL_image hPe hPi
      ⟨L, hL, hLQ, hfL⟩ hPQ (hinj.mono hPQ)
  let M := hfL.embeddedImage hinjL
  have hM : M.faces.Finite := hfL.embeddedImage_finite hinjL hL
  have hMs : M.space = f '' Q := by rw [hfL.embeddedImage_space, hLQ]
  have h0M : (0 : E) ∈ M.vertices := by
    rw [hfL.embeddedImage_vertices]
    exact ⟨0, h0L', hf0⟩
  have hMlink : (M.link 0).space = f '' (L.link 0).space := by
    simpa only [hf0] using hfL.embeddedImage_link_space hinjL h0L'
  have hP0M : P0.boundary ℝ = (M.link 0).space := by
    rw [hP0b, hPb, ← hMlink]
  let coords : E ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨C, forms, J, hC, hcv, h0C, hCV, hdisj, hstar,
    hforms, hrep, hJ, hJC⟩ :=
    M.exists_small_closedStar_halfspace_neighborhood hM h0M hV h0V coords
  obtain ⟨k, P1, hP1i, hP1e, hP1b⟩ :=
    M.exists_polygon_closedStar_convex_frontier hM P0 hP0e hP0i hP0M
      hC hcv h0C hdisj forms hforms hrep
  have hP1ne : ((M.closedStar 0).space ∩ frontier C).Nonempty := by
    rw [← hP1b]
    exact ⟨P1 0, P1.vertex_mem_boundary 0⟩
  have hSC : S ∩ C = M.space ∩ C := by
    ext x
    constructor
    · rintro ⟨hxS, hxC⟩
      exact ⟨hMs.symm.subset (hfull.subset ⟨hxS, hCV hxC⟩).1, hxC⟩
    · rintro ⟨hxM, hxC⟩
      exact ⟨(hfull.symm.subset ⟨hMs.subset hxM, hCV hxC⟩).1, hxC⟩
  have hcone : S ∩ C = convexJoin ℝ {0} (P1.boundary ℝ) := by
    rw [hSC, hP1b,
      M.convexJoin_closedStar_frontier_eq_inter hC hcv h0C hdisj hP1ne]
    exact hstar
  have hMint : interior M.space = ∅ := by
    apply M.interior_space_eq_empty_of_card_le hM
    intro s hs
    rw [hfL.embeddedImage_faces hinjL] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have htcard := (L.indep ht).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    have ht3 : t.card ≤ 3 := by simpa [Module.finrank_prod] using htcard
    rw [hdim]
    exact Finset.card_image_le.trans ht3
  obtain ⟨q, hq⟩ := M.exists_frontier_notMem_closedStar hMint
    (M.vertices_subset_space h0M) hC hcv h0C
  have hP1C : P1.boundary ℝ ⊆ frontier C := hP1b.subset.trans inter_subset_right
  have hqP : (q : E) ∉ P1.boundary ℝ := fun hx => hq (hP1b.subset hx).1
  obtain ⟨d0, d1, hd0, hd1, hcover, hinter, _⟩ :=
    J.exists_convex_sphere_polygon_cut hJ hC hcv ⟨0, h0C⟩ hJC hdim
      P1 hP1e hP1i hP1C q hqP
  obtain ⟨H, hHs, hHt, hH, hHi, hH0, hHS⟩ :=
    exists_conical_surface_chart hdim hC hcv h0C hd0 hd1 hcover hinter hcone
  exact ⟨H, hHs.symm.subset h0C,
    fun _ hx => hCV (interior_subset (hHs.subset hx)), hHt, hH, hHi, hH0, hHS⟩

end PoincareConjecture.M76.HamiltonIndexOne
