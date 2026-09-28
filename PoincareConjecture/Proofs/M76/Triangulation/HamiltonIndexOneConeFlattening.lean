import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneConeExtension
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoStandardPrism
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.Mathlib.ConvexConeIncidence

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V" => ((ℝ × ℝ) × ℝ)

private theorem upper_lower_outer_union :
    HamiltonIndexTwoStandard.upperOuter 0 1 ∪
      HamiltonIndexTwoStandard.lowerOuter (-1) 0 =
        frontier (CoordinateHalfBoxes.box 1) := by
  have hb := CoordinateHalfBoxes.box_ballPair (by norm_num : (0 : ℝ) < 1)
  have hfr := hb.frontier_eq_of_finrank_eq rfl
  rw [hfr]
  ext x
  change (((x.1 ∈ CoordinateHalfBoxes.baseBoundary 1 ∧ x.2 ∈ Icc 0 1) ∨
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 = 1)) ∨
    ((x.1 ∈ CoordinateHalfBoxes.baseBoundary 1 ∧ x.2 ∈ Icc (-1) 0) ∨
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 = -1))) ↔
    (x.1 ∈ CoordinateHalfBoxes.baseBoundary 1 ∧ x.2 ∈ Icc (-1) 1) ∨
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 ∈ ({-1, 1} : Set ℝ))
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl ⟨h.1, by linarith [h.2.1], h.2.2⟩
    · exact Or.inr ⟨h.1, Or.inr h.2⟩
    · exact Or.inl ⟨h.1, h.2.1, by linarith [h.2.2]⟩
    · exact Or.inr ⟨h.1, Or.inl h.2⟩
  · rintro (h | h)
    · rcases le_total 0 x.2 with hx | hx
      · exact Or.inl (Or.inl ⟨h.1, hx, h.2.2⟩)
      · exact Or.inr (Or.inl ⟨h.1, h.2.1, hx⟩)
    · rcases h.2 with hx | hx
      · exact Or.inr (Or.inr ⟨h.1, hx⟩)
      · exact Or.inl (Or.inr ⟨h.1, hx⟩)

private theorem upper_lower_outer_inter :
    HamiltonIndexTwoStandard.upperOuter 0 1 ∩
      HamiltonIndexTwoStandard.lowerOuter (-1) 0 =
        HamiltonIndexTwoStandard.endRim 0 := by
  ext x
  change (((x.1 ∈ CoordinateHalfBoxes.baseBoundary 1 ∧ x.2 ∈ Icc 0 1) ∨
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 = 1)) ∧
    ((x.1 ∈ CoordinateHalfBoxes.baseBoundary 1 ∧ x.2 ∈ Icc (-1) 0) ∨
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 = -1))) ↔
    x.1 ∈ CoordinateHalfBoxes.baseBoundary 1 ∧ x.2 = 0
  constructor
  · rintro ⟨h | h, k | k⟩
    · exact ⟨h.1, le_antisymm k.2.2 h.2.1⟩
    · linarith [h.2.1, k.2]
    · linarith [h.2, k.2.2]
    · linarith [h.2, k.2]
  · rintro ⟨hx, ht⟩
    rw [ht]
    exact ⟨Or.inl ⟨hx, le_rfl, zero_le_one⟩,
      Or.inl ⟨hx, by norm_num, le_rfl⟩⟩

theorem exists_equator_frontier_map {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C d₀ d₁ q : Set E}
    (h₀ : IsFinitePLBallPair (ℝ × ℝ) d₀ q)
    (h₁ : IsFinitePLBallPair (ℝ × ℝ) d₁ q)
    (hcover : d₀ ∪ d₁ = frontier C) (hinter : d₀ ∩ d₁ = q) :
    ∃ e : frontier C ≃ₜ frontier (CoordinateHalfBoxes.box 1),
      e.IsFinitePL ∧ ∀ x : frontier C,
        (x : E) ∈ q ↔ (e x : V) ∈ CoordinateHalfBoxes.rim 1 := by
  obtain ⟨e₁, he₁, he₁q⟩ := h₁.exists_homeomorph
    (HamiltonIndexTwoStandard.lowerOuter_ballPair (by norm_num : (-1 : ℝ) < 0))
  obtain ⟨H, hH, _, hH₀, hH₁⟩ := h₀.exists_union_homeomorph_of_boundary_piece
    (HamiltonIndexTwoStandard.upperOuter_ballPair (by norm_num : (0 : ℝ) < 1))
    hinter upper_lower_outer_inter e₁ he₁ he₁q
  let e := (Homeomorph.setCongr hcover.symm).trans
    (H.trans (Homeomorph.setCongr upper_lower_outer_union))
  refine ⟨e, hH.setCongr hcover upper_lower_outer_union, ?_⟩
  intro x
  change (x : E) ∈ q ↔
    (H ⟨x, hcover.symm ▸ x.property⟩ : V) ∈ HamiltonIndexTwoStandard.endRim 0
  rw [← hinter, ← upper_lower_outer_inter, mem_inter_iff, mem_inter_iff,
    hH₀ ⟨x, hcover.symm ▸ x.property⟩, hH₁ ⟨x, hcover.symm ▸ x.property⟩]

private theorem convexJoin_equator :
    convexJoin ℝ {(0 : V)} (CoordinateHalfBoxes.rim 1) =
      CoordinateHalfBoxes.disk 1 := by
  have hb := CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 1)
  have hfr := hb.frontier_eq_of_finrank_eq rfl
  have hcv : Convex ℝ (CoordinateHalfBoxes.base 1) :=
    (convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)
  have hzero : (0 : ℝ × ℝ) ∈ interior (CoordinateHalfBoxes.base 1) := by
    have hbball : CoordinateHalfBoxes.base 1 = Metric.closedBall (0 : ℝ × ℝ) 1 := by
      ext x
      simp only [CoordinateHalfBoxes.base, mem_prod, mem_Icc, Metric.mem_closedBall,
        dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
    rw [hbball]
    exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by norm_num))
  have hne : (frontier (CoordinateHalfBoxes.base 1)).Nonempty := by
    rw [hfr]
    exact ⟨(1, 0), by norm_num [CoordinateHalfBoxes.baseBoundary]⟩
  have hcone := hb.isCompact.convexJoin_zero_frontier_eq hcv hzero hne
  rw [hfr] at hcone
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, t, ht, rfl⟩ := (mem_convexJoin_zero_iff _ x).mp hx
    have hy' : y.1 ∈ CoordinateHalfBoxes.baseBoundary 1 ∧ y.2 = 0 := hy
    refine ⟨?_, ?_⟩
    · rw [← hcone]
      exact (mem_convexJoin_zero_iff _ _).mpr ⟨y.1, hy'.1, t, ht, rfl⟩
    · change t • y.2 = 0
      rw [hy'.2, smul_zero]
  · rintro ⟨hx, ht⟩
    change x.2 = 0 at ht
    have hx' : x.1 ∈ convexJoin ℝ {(0 : ℝ × ℝ)}
        (CoordinateHalfBoxes.baseBoundary 1) := hcone.symm ▸ hx
    obtain ⟨y, hy, t, ht', hxy⟩ := (mem_convexJoin_zero_iff _ _).mp hx'
    refine (mem_convexJoin_zero_iff _ _).mpr ⟨(y, 0), ⟨hy, rfl⟩, t, ht', ?_⟩
    apply Prod.ext
    · exact hxy
    · simpa only [Prod.smul_snd, smul_zero] using ht

theorem exists_conical_surface_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    {C S d₀ d₁ q : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C)
    (h₀ : IsFinitePLBallPair (ℝ × ℝ) d₀ q)
    (h₁ : IsFinitePLBallPair (ℝ × ℝ) d₁ q)
    (hcover : d₀ ∪ d₁ = frontier C) (hinter : d₀ ∩ d₁ = q)
    (hsection : S ∩ C = convexJoin ℝ {0} q) :
    ∃ H : OpenPartialHomeomorph E V,
      H.source = interior C ∧ H.target = interior (CoordinateHalfBoxes.box 1) ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧ H 0 = 0 ∧
      ∀ x ∈ H.source, x ∈ S ↔ (H x).2 = 0 := by
  obtain ⟨e, he, heq⟩ := exists_equator_frontier_map h₀ h₁ hcover hinter
  have hbox := CoordinateHalfBoxes.box_ballPair (by norm_num : (0 : ℝ) < 1)
  have hboxcv : Convex ℝ (CoordinateHalfBoxes.box 1) := by
    rw [CoordinateHalfBoxes.box_eq_closedBall]
    exact convex_closedBall (0 : V) 1
  obtain ⟨g, G, hG, hGg, hg0, hrad⟩ := exists_radial_convex_extension
    he hC hbox.isCompact hcv hboxcv hzero
    (CoordinateHalfBoxes.zero_mem_interior_box (by norm_num : (0 : ℝ) < 1))
  have hq : q ⊆ frontier C := fun x hx => hcover ▸ Or.inl (h₀.1 hx)
  have heimage : (fun x : frontier C => (e x : V)) ''
      ((Subtype.val : frontier C → E) ⁻¹' q) = CoordinateHalfBoxes.rim 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (heq x).mp hx
    · intro hy
      have hyfr : y ∈ frontier (CoordinateHalfBoxes.box 1) := by
        rw [← upper_lower_outer_union]
        exact Or.inl ((HamiltonIndexTwoStandard.upperOuter_ballPair
          (by norm_num : (0 : ℝ) < 1)).1 hy)
      refine ⟨e.symm ⟨y, hyfr⟩, ?_, ?_⟩
      · exact (heq _).mpr (by simpa only [e.apply_symm_apply] using hy)
      · exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hyfr⟩)
  have himage : g '' (S ∩ C) = CoordinateHalfBoxes.disk 1 := by
    rw [hsection, radial_extension_image_convexJoin e g hrad hq,
      heimage, convexJoin_equator]
  obtain ⟨H, hHs, hHt, hHPL, hiHPL, _, _, hHG, _⟩ :=
    hG.exists_interior_chart (by simpa [Module.finrank_prod] using hdim)
  have hHg (x : E) (hx : x ∈ C) : H x = g x :=
    (hHG ⟨x, hx⟩).trans (hGg ⟨x, hx⟩)
  refine ⟨H, hHs, hHt, hHPL, hiHPL, (hHg 0 (interior_subset hzero)).trans hg0, ?_⟩
  intro x hx
  have hxC : x ∈ C := interior_subset (hHs ▸ hx)
  have hHx : H x ∈ CoordinateHalfBoxes.box 1 :=
    interior_subset (hHt ▸ H.map_source hx)
  have hplane : H x ∈ CoordinateHalfBoxes.disk 1 ↔ (H x).2 = 0 := by
    rw [← CoordinateHalfBoxes.box_inter_plane (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨fun h => h.2, fun h => ⟨hHx, h⟩⟩
  rw [← hplane]
  constructor
  · intro hxS
    rw [← himage, hHg x hxC]
    exact mem_image_of_mem g ⟨hxS, hxC⟩
  · intro hxs
    have hxs' : g x ∈ g '' (S ∩ C) := by
      rw [himage, ← hHg x hxC]
      exact hxs
    obtain ⟨y, hy, hyx⟩ := hxs'
    have hyx' : G ⟨y, hy.2⟩ = G ⟨x, hxC⟩ := by
      apply Subtype.ext
      simpa only [hGg] using hyx
    have hyxeq : y = x := congrArg Subtype.val (G.injective hyx')
    exact hyxeq ▸ hy.1

end PoincareConjecture.M76.HamiltonIndexOne
