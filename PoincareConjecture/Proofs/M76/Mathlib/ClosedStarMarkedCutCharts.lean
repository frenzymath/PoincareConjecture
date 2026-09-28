import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarHalfspaceCuts










set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
  {ι κ : Type*} [Finite ι] [Nonempty ι] [Finite κ]




theorem exists_finitePL_closedStar_chart_preserving_cut_family
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hz : (0 : E) ∈ K.vertices) (hint : (0 : E) ∈ interior K.space)
    (c : E ≃L[ℝ] (ι → ℝ)) (A : κ → E →ₗ[ℝ] ℝ) :
    ∃ (C : Set E) (L : (ι ⊕ ι) → E →ₗ[ℝ] ℝ)
      (H : (K.closedStar 0).space ≃ₜ C),
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧
      (∀ i, L i ≠ 0) ∧ C = {x | ∀ i, L i x ≤ 1} ∧ H.IsFinitePL ∧
      (∀ x : (K.closedStar 0).space,
        (x : E) ∈ (K.link 0).space ↔ (H x : E) ∈ frontier C) ∧
      ∀ j (x : (K.closedStar 0).space),
        (A j (H x : E) = 0 ↔ A j (x : E) = 0) ∧
        (0 ≤ A j (H x : E) ↔ 0 ≤ A j (x : E)) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let L := K.link 0
  have hL : L.faces.Finite := finite_link_faces hK 0
  let n := hL.toFinset.sup Finset.card
  have hn (s : Finset E) (hs : s ∈ L.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hL.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  let F : Finset (E →ᵃ[ℝ] ℝ) := Finset.univ.image (fun j => (A j).toAffineMap)
  obtain ⟨R, hR, hRL, _, hRA⟩ :=
    L.exists_subdivision_respectsAffineHyperplanes hL hn F
  have hlin := hRL.linearIndependent_faces
    (fun _ hs => linearIndependent_of_mem_link_zero hs)
  have hrad : InjOn (NormedSpace.normalize : E → E) R.space :=
    K.injOn_normalize_link.mono hRL.space_eq.subset
  let J := R.coneAtZero hlin hrad
  have hJ : J.faces.Finite := finite_coneAtZero_faces hR hlin hrad
  have hJstar : J.closedStar 0 = J := R.closedStar_coneAtZero hlin hrad
  have hJlink : (J.link 0).space = (K.link 0).space := by
    rw [show J.link 0 = R from R.link_coneAtZero hlin hrad]
    exact hRL.space_eq
  have hstarint : (0 : E) ∈ interior (K.closedStar 0).space := by
    obtain ⟨ε, hε, hsub⟩ := K.exists_ball_inter_space_subset_closedStar hK hz
    have hV : interior K.space ∩ ball (0 : E) ε ⊆ (K.closedStar 0).space :=
      fun _ hx => hsub ⟨interior_subset hx.1, hx.2⟩
    exact interior_maximal hV (isOpen_interior.inter isOpen_ball)
      ⟨hint, mem_ball_self hε⟩
  have hne : L.space.Nonempty := by
    obtain ⟨C, _, H, hC, _, hC0, _, _, _, hboundary, _⟩ :=
      K.exists_finitePL_closedStar_chart_preserving_halfspaces hK hz hint c
    obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr
      ⟨⟨0, interior_subset hC0⟩, hC.ne_univ⟩
    exact ⟨H.symm ⟨x, hC.isClosed.frontier_subset hx⟩,
      (hboundary _).mpr (by simpa only [H.apply_symm_apply] using hx)⟩
  have hJs : J.space = (K.closedStar 0).space := by
    rw [R.coneAtZero_space_eq_convexJoin hlin hrad (hRL.space_eq.symm ▸ hne),
      hRL.space_eq, ← coneAtZero_link_eq_closedStar K hz]
    exact ((K.link 0).coneAtZero_space_eq_convexJoin
      (fun _ hs => linearIndependent_of_mem_link_zero hs) K.injOn_normalize_link hne).symm
  have hzJ : (0 : E) ∈ J.vertices := zero_mem_coneAtZero_vertices hlin hrad
  have hJA (j : κ) : (J.link 0).RespectsAffineHyperplane (A j).toAffineMap := by
    rw [show J.link 0 = R from R.link_coneAtZero hlin hrad]
    exact hRA _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  obtain ⟨C, B, H, hC, hcv, hC0, hB, hrep, hH, hboundary, hmarks⟩ :=
    J.exists_finitePL_closedStar_chart_preserving_halfspaces
      hJ hzJ (hJs.symm ▸ hstarint) c
  have hsource : (J.closedStar 0).space = (K.closedStar 0).space := by
    rw [hJstar, hJs]
  let e := (Homeomorph.setCongr hsource.symm).trans H
  refine ⟨C, B, e, hC, hcv, hC0, hB, hrep, hH.setCongr hsource rfl, ?_, ?_⟩
  · intro x
    have h := hboundary ⟨x, hsource.symm.subset x.property⟩
    change ((x : E) ∈ (K.link 0).space) ↔
      (H ⟨x, hsource.symm.subset x.property⟩ : E) ∈ frontier C
    simpa only [hJlink] using h
  · intro j x
    exact hmarks (A j) (hJA j) ⟨x, hsource.symm.subset x.property⟩

end Geometry.SimplicialComplex
