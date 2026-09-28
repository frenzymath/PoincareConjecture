import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneConeFlattening
import PoincareConjecture.Proofs.M76.Triangulation.ConvexSpherePolygonCut
import PoincareConjecture.Proofs.M76.Mathlib.TranslatedOriginalEventBody
import PoincareConjecture.Proofs.M76.Mathlib.SurfaceLinkPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskStarSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarPurity
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarConnectedLinks

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V" => ((ℝ × ℝ) × ℝ)

theorem exists_surface_chart_of_local_ball_pairs {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hlocal : ∀ x : K.space, ∃ d q : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d q ∧ d ⊆ K.space ∧ (x : E) ∈ d \ q ∧
        IsOpen ((Subtype.val : K.space → E) ⁻¹' (d \ q)))
    {p : E} (hp : p ∈ K.space) :
    ∃ H : OpenPartialHomeomorph E V, p ∈ H.source ∧ H p = 0 ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      ∀ x ∈ H.source, x ∈ K.space ↔ (H x).2 = 0 := by
  classical
  obtain ⟨T, hT, hTK, _, hstars⟩ :=
    K.exists_faceAffine_vertex_stars_of_local_ball_pairs hK hlocal (0 : E →ᵃ[ℝ] ℝ)
  have hdim2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hpure : ∀ s ∈ T.faces, ∃ t ∈ T.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, htc⟩ := T.exists_full_coface_of_faceAffine_vertex_stars
      hT hstars s hs
    exact ⟨t, ht, by simpa only [hdim2] using htc, hst⟩
  have hcofaces : ∀ s ∈ T.faces, s.card = 2 →
      {t : Finset E | t ∈ T.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
    intro s hs hsc
    have hlink := T.faceLink_ncard_eq_two_of_faceAffine_vertex_stars hT hstars s hs
      (hsc.trans hdim2.symm)
    rw [T.ncard_faceLink_vertices_eq_cofaces, hsc] at hlink
    exact hlink
  have hlinks : ∀ x ∈ T.vertices, IsConnected (T.link x).space := by
    intro x hx
    have hlink := T.isConnected_faceLink_of_faceAffine_vertex_stars hT hstars {x} hx
      (by simp [hdim2])
    simpa only [SimplicialComplex.faceLink_singleton_eq_link] using hlink
  let τ : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have hτp : τ p = 0 := by change -p + p = 0; exact neg_add_cancel p
  let coords : E ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hdim])
  obtain ⟨M, C, L, J, _, hT0, _, hM, hMT, hzeroM, hpureM, hcofacesM,
    hconn, hC, hcv, hzeroC, _, hdisj, hstar, _, hL, hrep, hJ, hJC, _⟩ :=
    T.exists_original_event_body_in_centered_coordinates hT hpure hcofaces hlinks
      (hTK.space_eq.symm ▸ hp) τ hτp isOpen_univ (mem_univ p) coords
  have hMspace : M.space = τ '' K.space := by
    rw [hMT, hT0, hTK.space_eq]
  obtain ⟨n, P, hPi, hPe, hPb⟩ :=
    M.exists_surface_link_polygon hM hpureM hcofacesM 0 hconn
  obtain ⟨N, Q, hQi, hQe, hQb⟩ :=
    M.exists_polygon_closedStar_convex_frontier hM P hPe hPi hPb
      hC hcv hzeroC hdisj L hL hrep
  have hQne : ((M.closedStar 0).space ∩ frontier C).Nonempty := by
    rw [← hQb]
    exact ⟨Q 0, Q.vertex_mem_boundary 0⟩
  have hcone : M.space ∩ C = convexJoin ℝ {0} (Q.boundary ℝ) := by
    rw [hQb, M.convexJoin_closedStar_frontier_eq_inter hC hcv hzeroC hdisj hQne]
    exact hstar
  have hint : interior M.space = ∅ := by
    apply M.interior_space_eq_empty_of_card_le hM
    intro s hs
    obtain ⟨t, _, htc, hst⟩ := hpureM s hs
    rw [hdim]
    exact (Finset.card_le_card hst).trans_eq htc
  obtain ⟨a, ha⟩ := M.exists_frontier_notMem_closedStar hint
    (M.vertices_subset_space hzeroM) hC hcv hzeroC
  have hQC : Q.boundary ℝ ⊆ frontier C := hQb.subset.trans inter_subset_right
  have haQ : (a : E) ∉ Q.boundary ℝ := fun hx => ha (hQb.subset hx).1
  obtain ⟨d₀, d₁, hd₀, hd₁, hcover, hinter, _⟩ :=
    J.exists_convex_sphere_polygon_cut hJ hC hcv ⟨0, hzeroC⟩ hJC hdim Q hQe hQi hQC a haQ
  obtain ⟨H, hHs, hHt, hHPL, hHiPL, hH0, hHS⟩ :=
    exists_conical_surface_chart hdim hC hcv hzeroC hd₀ hd₁ hcover hinter hcone
  let B := τ.toHomeomorph.toOpenPartialHomeomorph.trans H
  have hpB : p ∈ B.source := by
    change p ∈ (univ : Set E) ∧ τ p ∈ H.source
    exact ⟨mem_univ p, by rw [hτp, hHs]; exact hzeroC⟩
  have hBt : B.target = interior (CoordinateHalfBoxes.box 1) := by
    change H.target ∩ H.symm ⁻¹' (univ : Set E) = _
    simp only [preimage_univ, inter_univ, hHt]
  have hBPL : LocallyPiecewiseAffineOn B B.source :=
    hHPL.comp (locallyPiecewiseAffineOn_affine τ.toContinuousAffineMap isOpen_univ)
  have hBiPL : LocallyPiecewiseAffineOn B.symm B.target :=
    (locallyPiecewiseAffineOn_affine τ.symm.toContinuousAffineMap isOpen_univ).comp hHiPL
  refine ⟨B, hpB, ?_, hBt, hBPL, hBiPL, ?_⟩
  · change H (τ p) = 0
    rw [hτp, hH0]
  · intro x hx
    have hτx : τ x ∈ M.space ↔ x ∈ K.space := by
      rw [hMspace]
      constructor
      · rintro ⟨y, hy, heq⟩
        exact τ.injective heq ▸ hy
      · intro h
        exact mem_image_of_mem τ h
    exact hτx.symm.trans (hHS (τ x) hx.2)

end PoincareConjecture.M76.HamiltonIndexOne
