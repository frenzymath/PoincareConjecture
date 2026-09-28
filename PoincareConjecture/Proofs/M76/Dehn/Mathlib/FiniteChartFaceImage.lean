import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartImageIntersection
import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex



theorem vertexSubcomplex_face_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) {σ : Finset E} (hσ : σ ∈ K.faces) :
    (K.vertexSubcomplex (σ : Set E)).space = convexHull ℝ (σ : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨τ, hτ, hxτ⟩ := mem_space_iff.mp hx
    exact convexHull_mono (fun v hv => hτ.2 v hv) hxτ
  · intro hx
    exact mem_space_iff.mpr ⟨σ, ⟨hσ, fun _ hv => hv⟩, hx⟩

end Geometry.SimplicialComplex

namespace Geometry





theorem PolyhedralPLInCharts.exists_finite_face_chart_image
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    {σ : Finset E} (hσ : σ ∈ K.faces)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) :
    ∃ L : SimplicialComplex ℝ F, L.faces.Finite ∧
      L.space = Q '' (f '' convexHull ℝ (σ : Set E) ∩ Q.source) ∩ J.space ∧
      ∀ τ ∈ L.faces, τ.card ≤ σ.card := by
  classical
  let Kσ := K.vertexSubcomplex (σ : Set E)
  have hKσ : Kσ.faces.Finite := K.vertexSubcomplex_finite (σ : Set E) hK
  have hKσs : Kσ.space = convexHull ℝ (σ : Set E) := K.vertexSubcomplex_face_space hσ
  have hKσK : Kσ.space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (K.vertexSubcomplex_le (σ : Set E))
  have hfσ := hf.restrict_finite Kσ hKσ hKσK
  let : CompactSpace Kσ.space := isCompact_iff_compactSpace.mp
    (Kσ.isCompact_space_of_finite hKσ)
  let A : Set Kσ.space := (fun x => f x) ⁻¹' (Q.symm '' J.space)
  let O : Set Kσ.space := (fun x => f x) ⁻¹' Q.source
  have hcompact : IsCompact (Q.symm '' J.space) :=
    (J.isCompact_space_of_finite hJ).image_of_continuousOn
      (Q.symm.continuousOn.mono hJQ)
  have hA : IsCompact A :=
    (hcompact.isClosed.preimage hfσ.continuousOn.domRestrict).isCompact
  have hO : IsOpen O := Q.open_source.preimage hfσ.continuousOn.domRestrict
  have hAO : A ⊆ O := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hx
    change Q.symm y = f x at heq
    change f x ∈ Q.source
    rw [← heq]
    exact Q.map_target (hJQ hy)
  obtain ⟨N, V, hN, hNKσ, _, hAV, hVN, hNO⟩ :=
    Kσ.exists_relative_compact_polyhedral_neighborhood hKσ hA hO hAO
  have hNQ : MapsTo f N.space Q.source := by
    intro x hx
    exact hNO (show (⟨x, hNKσ hx⟩ : Kσ.space) ∈ Subtype.val ⁻¹' N.space from hx)
  have hfN := hf.restrict_finite N hN (hNKσ.trans hKσK)
  obtain ⟨T, hT, hTs, hcoords⟩ :=
    hfN.finitePiecewiseAffineOn_compatible_chart_finite_source N hN Q hQ hNQ
  have hTdim (τ : Finset E) (hτ : τ ∈ T.faces) : τ.card ≤ σ.card := by
    apply (T.indep hτ).card_le_card_of_subset_affineSpan
    intro x hx
    have hxN : x ∈ N.space := hTs.subset (T.subset_space hτ hx)
    exact convexHull_subset_affineSpan (s := (σ : Set E)) (hKσs.subset (hNKσ hxN))
  obtain ⟨B, hB, hBs, hBfaces⟩ := hcoords.exists_finite_triangulation_image hT
  have hBdim (τ : Finset F) (hτ : τ ∈ B.faces) : τ.card ≤ σ.card := by
    obtain ⟨s, hs, _, hcard⟩ := hBfaces τ hτ
    exact hcard.trans (hTdim s hs)
  obtain ⟨L, hL, hLs⟩ := B.exists_finite_triangulation_inter J hB hJ
  have hLexact : L.space =
      Q '' (f '' convexHull ℝ (σ : Set E) ∩ Q.source) ∩ J.space := by
    rw [hLs, hBs, hTs]
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨⟨f x, ⟨mem_image_of_mem f (hKσs.subset (hNKσ hx)), hNQ hx⟩, rfl⟩, hz⟩
    · rintro ⟨⟨y, ⟨⟨x, hx, rfl⟩, hfx⟩, rfl⟩, hz⟩
      have hxKσ : x ∈ Kσ.space := hKσs.symm.subset hx
      have hxA : (⟨x, hxKσ⟩ : Kσ.space) ∈ A :=
        ⟨Q (f x), hz, Q.left_inv hfx⟩
      have hxN : x ∈ N.space :=
        hVN (mem_image_of_mem Subtype.val (hAV hxA))
      exact ⟨⟨x, hxN, rfl⟩, hz⟩
  have hLB : L.space ⊆ B.space := hLs.subset.trans inter_subset_left
  obtain ⟨R, P, hR, hRB, hP⟩ :=
    B.exists_subdivision_with_finite_full_polyhedra hB (fun _ : Unit => L)
      (fun _ => hL) (fun _ => hLB)
  refine ⟨P (), hR.subset (hP ()).1, (hP ()).2.1.trans hLexact, ?_⟩
  intro τ hτ
  obtain ⟨s, hs, hτs⟩ := hRB.face_subset τ ((hP ()).1 hτ)
  have hspan : (τ : Set F) ⊆ affineSpan ℝ (s : Set F) :=
    (subset_convexHull ℝ _).trans (hτs.trans (convexHull_subset_affineSpan _))
  exact (((P ()).indep hτ).card_le_card_of_subset_affineSpan hspan).trans (hBdim s hs)

end Geometry
