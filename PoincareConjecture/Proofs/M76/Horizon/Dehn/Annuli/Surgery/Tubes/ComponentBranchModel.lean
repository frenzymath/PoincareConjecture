import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.ComponentAxisModel

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

structure ComponentBranchModel
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    (old : SourceCircleDecomposition f S) (i : old.Index) where
  sample : Finset (f '' old.pieces i)
  graph : X → (sample → ℝ × V3)
  core : Set X
  complex : SimplicialComplex ℝ (sample → ℝ × V3)
  axis : SimplicialComplex ℝ (sample → ℝ × V3)
  sourceImage : SimplicialComplex ℝ (sample → ℝ × V3)
  source : SimplicialComplex ℝ E
  homeomorph : core ≃ₜ complex.space
  inverse : (sample → ℝ × V3) → core
  charts : f '' old.pieces i → OpenPartialHomeomorph X V3
  core_compact : IsCompact core
  core_neighborhood : f '' old.pieces i ⊆ interior core
  graph_continuous : Continuous graph
  graph_separates : ∀ x ∈ core, ∀ y : X, graph x = graph y → x = y
  complex_finite : complex.faces.Finite
  axis_le : axis ≤ complex
  axis_full : ∀ t ∈ complex.faces, (∀ v ∈ t, v ∈ axis.vertices) → t ∈ axis.faces
  complex_space : complex.space = graph '' core
  axis_space : axis.space = (graph ∘ f) '' old.pieces i
  homeomorph_value : ∀ x : core, (homeomorph x : sample → ℝ × V3) = graph x
  inverse_value : ∀ z : complex.space, (inverse z : X) = (homeomorph.symm z : X)
  inverse_PL : PolyhedralPLInCharts e (fun z ↦ (inverse z : X)) complex.space
  selected_PL : FinitePiecewiseAffineOn (graph ∘ f) (old.pieces i)
  chart_point : ∀ y, (y : X) ∈ (charts y).source
  chart_compatible : ∀ y k, (e k).symm.trans (charts y) ∈ piecewiseAffineGroupoid V3
  chart_axis : ∀ y z, z ∈ (charts y).source →
    (z ∈ f '' old.pieces i ↔ z ∈ R ∧ charts y z 0 = 0 ∧ charts y z 1 = 0)
  raw_charts : ∀ z : f '' old.pieces i, ∃ (x y : E) (D : RawSourceCrossing e f S R x y),
    f x = z ∧ (charts z : X → V3) = D.chart ∧ (charts z).source ⊆ D.chart.source
  selected_stars : ∀ p ∈ axis.vertices, ∃ y : f '' old.pieces i,
    MapsTo (fun z ↦ (inverse z : X)) (complex.closedStar p).space (charts y).source ∧
    (complex.closedStar p).AffineOnFaces (fun z ↦ charts y (inverse z))
  sourceImage_le : sourceImage ≤ complex
  sourceImage_full : ∀ t ∈ complex.faces, (∀ v ∈ t, v ∈ sourceImage.vertices) →
    t ∈ sourceImage.faces
  source_finite : source.faces.Finite
  source_space : source.space = S ∩ f ⁻¹' core
  source_PL : FinitePiecewiseAffineOn (graph ∘ f) source.space
  source_image : sourceImage.space = (graph ∘ f) '' source.space

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
  {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
  {old : SourceCircleDecomposition f S} {i : old.Index}

theorem SourceCircleDecomposition.exists_component_branch_model [T2Space X]
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite) (hQS : Q.space = S)
    (old : SourceCircleDecomposition f S) (hf : PolyhedralPLInCharts e f S)
    (he : PLDomain e R)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y))
    (i : old.Index) {W : Set X} (hW : IsOpen W) (hAW : f '' old.pieces i ⊆ W) :
    ∃ D : ComponentBranchModel (e := e) (R := R) old i, D.core ⊆ W ∧
      ∀ y, (D.charts y).source ⊆ W := by
  subst S
  obtain ⟨s, F, C, K, A, H, g, B, hC, hAC, hCW, hFc, hsep, hK, hAK, hfull,
    hKs, hAs, hH, hg, hgPL, hF, hB, hstar, hraw, N, T, hNK, hNfull,
    hT, hTs, hTPL, hNs⟩ :=
    SourceCircleDecomposition.exists_component_axis_model_with_raw_branches
      Q hQ old hf he hcross i hW hAW
  exact ⟨{
    sample := s, graph := F, core := C, complex := K, axis := A, sourceImage := N,
    source := T, homeomorph := H, inverse := g, charts := B,
    core_compact := hC, core_neighborhood := hAC, graph_continuous := hFc,
    graph_separates := hsep, complex_finite := hK, axis_le := hAK, axis_full := hfull,
    complex_space := hKs, axis_space := hAs, homeomorph_value := hH,
    inverse_value := hg, inverse_PL := hgPL, selected_PL := hF,
    chart_point := fun y ↦ (hB y).1, chart_compatible := fun y ↦ (hB y).2.2.1,
    chart_axis := fun y ↦ (hB y).2.2.2, raw_charts := hraw, selected_stars := hstar,
    sourceImage_le := hNK, sourceImage_full := hNfull, source_finite := hT,
    source_space := hTs, source_PL := hTPL, source_image := hNs }, hCW,
    fun y ↦ (hB y).2.1⟩

theorem ComponentBranchModel.graph_inverse (D : ComponentBranchModel (e := e) (R := R) old i)
    (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) : D.graph (D.inverse z) = z := by
  rw [← D.homeomorph_value]
  have heq : D.inverse z = D.homeomorph.symm ⟨z, hz⟩ := Subtype.ext (D.inverse_value ⟨z, hz⟩)
  rw [heq, D.homeomorph.apply_symm_apply]

theorem ComponentBranchModel.mem_sourceImage (D : ComponentBranchModel (e := e) (R := R) old i)
    (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) :
    z ∈ D.sourceImage.space ↔ (D.inverse z : X) ∈ f '' S := by
  rw [D.source_image]
  constructor
  · rintro ⟨x, hx, hfx⟩
    have hx' := D.source_space.subset hx
    refine ⟨x, hx'.1, ?_⟩
    exact D.graph_separates (f x) hx'.2 (D.inverse z)
      (hfx.trans (D.graph_inverse z hz).symm)
  · rintro ⟨x, hx, hfx⟩
    refine ⟨x, D.source_space.symm.subset ⟨hx, ?_⟩, ?_⟩
    · change f x ∈ D.core
      rw [hfx]
      exact (D.inverse z).property
    · change D.graph (f x) = z
      rw [hfx, D.graph_inverse z hz]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in

theorem RawSourceCrossing.source_image_iff
    {x y : E} (C : RawSourceCrossing e f S R x y)
    (z : X) (hz : z ∈ C.chart.source) :
    z ∈ f '' S ↔ z ∈ R ∧ (C.chart z 0 = 0 ∨ C.chart z 1 = 0) := by
  have h : z ∈ f '' S ↔ z ∈ f '' C.left ∪ f '' C.right := by
    constructor
    · rintro ⟨a, ha, haz⟩
      have ha' := C.whole_preimage.subset ⟨ha, by change f a ∈ C.chart.source; rwa [haz]⟩
      exact ha'.elim (fun hL => Or.inl ⟨a, hL, haz⟩) (fun hR => Or.inr ⟨a, hR, haz⟩)
    · rintro (⟨a, ha, haz⟩ | ⟨a, ha, haz⟩)
      · exact ⟨a, C.left_subset ha, haz⟩
      · exact ⟨a, C.right_subset ha, haz⟩
  rw [h, mem_union, C.left_image z hz, C.right_image z hz]
  tauto

theorem ComponentBranchModel.exists_raw_star (D : ComponentBranchModel (e := e) (R := R) old i)
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    ∃ (x y : E) (C : RawSourceCrossing e f S R x y),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      ∀ z ∈ (D.complex.closedStar p).space,
        z ∈ D.sourceImage.space ↔ (D.inverse z : X) ∈ R ∧
          (C.chart (D.inverse z) 0 = 0 ∨ C.chart (D.inverse z) 1 = 0) := by
  obtain ⟨q, hmap, hface⟩ := D.selected_stars p hp
  obtain ⟨x, y, C, _, hB, hBC⟩ := D.raw_charts q
  refine ⟨x, y, C, fun _ hz => hBC (hmap hz), ?_, ?_⟩
  · simpa only [hB] using hface
  · intro z hz
    rw [D.mem_sourceImage z (SimplicialComplex.space_subset_of_le
      (show D.complex.closedStar p ≤ D.complex from fun _ ht => ht.1) hz)]
    exact C.source_image_iff _ (hBC (hmap hz))

end PoincareConjecture.M76.Dehn.Annuli
