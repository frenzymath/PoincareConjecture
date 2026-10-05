import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.SourceRefinement
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Coordinates.Mathlib.FiniteChartImageIntersection

/-! # The actual finite edge carrier in mixed pair-chart coordinates -/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76.CollarMesh

theorem finitePL_in_mixed_chart
    {D E V X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {f : D → X} (hf : PolyhedralPLInCharts e f K.space)
    (Q : OpenPartialHomeomorph X E)
    (hQ : ∀ i, LocallyPiecewiseAffineOn ((e i).symm.trans Q) ((e i).symm.trans Q).source)
    (himage : MapsTo f K.space Q.source) :
    FinitePiecewiseAffineOn (Q ∘ f) K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, N, V, _, hNK, hV, hxV, hVN, hfi, hcoords⟩ := hf.coordinates x
  have hresult := (hQ i).comp_finitePiecewiseAffineOn hcoords (by
    intro y hy
    change e i (f y) ∈ (e i).target ∧ (e i).symm (e i (f y)) ∈ Q.source
    refine ⟨(e i).mapsTo (hfi hy), ?_⟩
    rw [(e i).left_inv (hfi hy)]
    exact himage (hNK hy))
  have hfixed : FinitePiecewiseAffineOn (Q ∘ f) N.space := hresult.congr (by
    intro y hy
    change Q ((e i).symm (e i (f y))) = Q (f y)
    rw [(e i).left_inv (hfi hy)])
  obtain ⟨J, hJ, hJN, hJF⟩ := hfixed
  exact ⟨J, V, hJ, hV, hxV, fun y hy => hJN.symm.subset (hVN hy), hJF⟩

theorem exists_mixed_chart_edge_carrier
    {D E V X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] [T2Space X] {e : ι → OpenPartialHomeomorph X V}
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2)
    {f : D → X} (hf : PolyhedralPLInCharts e f K.space)
    (Q : OpenPartialHomeomorph X E)
    (hQ : ∀ i, LocallyPiecewiseAffineOn ((e i).symm.trans Q) ((e i).symm.trans Q).source)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧
      ∀ z ∈ J.space, Q.symm z ∈ f '' K.space ↔ z ∈ L.space := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (K.isCompact_space_of_finite hK)
  let A : Set K.space := (fun x => f x) ⁻¹' (Q.symm '' J.space)
  let O : Set K.space := (fun x => f x) ⁻¹' Q.source
  have hcompact : IsCompact (Q.symm '' J.space) :=
    (J.isCompact_space_of_finite hJ).image_of_continuousOn (Q.symm.continuousOn.mono hJQ)
  have hA : IsCompact A := (hcompact.isClosed.preimage hf.continuousOn.domRestrict).isCompact
  have hO : IsOpen O := Q.open_source.preimage hf.continuousOn.domRestrict
  have hAO : A ⊆ O := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hx
    change Q.symm y = f x at heq
    change f x ∈ Q.source
    rw [← heq]
    exact Q.map_target (hJQ hy)
  obtain ⟨N, W, hN, hNK, _, hAW, hWN, hNO⟩ :=
    K.exists_relative_compact_polyhedral_neighborhood hK hA hO hAO
  have hNQ : MapsTo f N.space Q.source := by
    intro x hx
    exact hNO (show (⟨x, hNK hx⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hx)
  have hfN := hf.restrict_finite N hN hNK
  obtain ⟨P, hP, hPs, hPf⟩ := finitePL_in_mixed_chart N hN hfN Q hQ hNQ
  have hPc : ∀ s ∈ P.faces, s.card ≤ 2 := fun s hs =>
    P.face_card_le_of_hull_subset_finite_carrier K hK hs
      ((P.convexHull_subset_space hs).trans (hPs.subset.trans hNK)) hcard
  obtain ⟨B, hB, hBs, hBc⟩ := hPf.exists_finite_triangulation_image hP
  have hBcard : ∀ s ∈ B.faces, s.card ≤ 2 := by
    intro s hs
    obtain ⟨t, ht, _, hst⟩ := hBc s hs
    exact hst.trans (hPc t ht)
  obtain ⟨L, hL, hLs⟩ := B.exists_finite_triangulation_inter J hB hJ
  have hLcard : ∀ s ∈ L.faces, s.card ≤ 2 := fun s hs =>
    L.face_card_le_of_hull_subset_finite_carrier B hB hs
      ((L.convexHull_subset_space hs).trans (hLs.subset.trans inter_subset_left)) hBcard
  have heq : L.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space := by
    rw [hLs, hBs, hPs]
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨⟨f x, ⟨mem_image_of_mem f (hNK hx), hNQ hx⟩, rfl⟩, hz⟩
    · rintro ⟨⟨y, ⟨⟨x, hx, rfl⟩, hfx⟩, rfl⟩, hz⟩
      have hxA : (⟨x, hx⟩ : K.space) ∈ A := ⟨Q (f x), hz, Q.left_inv hfx⟩
      have hxN : x ∈ N.space := hWN (mem_image_of_mem Subtype.val (hAW hxA))
      exact ⟨⟨x, hxN, rfl⟩, hz⟩
  refine ⟨L, hL, heq, hLcard, ?_⟩
  intro z hz
  rw [heq]
  constructor
  · intro hs
    exact ⟨⟨Q.symm z, ⟨hs, Q.map_target (hJQ hz)⟩, Q.right_inv (hJQ hz)⟩, hz⟩
  · rintro ⟨⟨x, ⟨hx, hxQ⟩, rfl⟩, _⟩
    simpa only [Q.left_inv hxQ] using hx

end PoincareMT.M76.CollarMesh
