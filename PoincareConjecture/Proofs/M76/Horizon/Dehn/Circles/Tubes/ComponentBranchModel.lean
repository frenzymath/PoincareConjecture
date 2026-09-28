import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentAxisModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPartnerPL

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

structure ComponentBranchModel
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (i : old.Index) where
  sample : Finset (f '' old.pieces i)
  graph : X → (sample → ℝ × V3)
  core : Set X
  complex : SimplicialComplex ℝ (sample → ℝ × V3)
  axis : SimplicialComplex ℝ (sample → ℝ × V3)
  diskImage : SimplicialComplex ℝ (sample → ℝ × V3)
  source : SimplicialComplex ℝ V2
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
  raw_charts : ∀ z : f '' old.pieces i, ∃ (x y : V2) (D : RawCrossingChart e f R x y),
    f x = z ∧ (charts z : X → V3) = D.chart ∧ (charts z).source ⊆ D.chart.source
  selected_stars : ∀ p ∈ axis.vertices, ∃ y : f '' old.pieces i,
    MapsTo (fun z ↦ (inverse z : X)) (complex.closedStar p).space (charts y).source ∧
    (complex.closedStar p).AffineOnFaces (fun z ↦ charts y (inverse z))
  diskImage_le : diskImage ≤ complex
  diskImage_full : ∀ t ∈ complex.faces, (∀ v ∈ t, v ∈ diskImage.vertices) →
    t ∈ diskImage.faces
  source_finite : source.faces.Finite
  source_space : source.space = D2 ∩ f ⁻¹' core
  source_PL : FinitePiecewiseAffineOn (graph ∘ f) source.space
  source_image : diskImage.space = (graph ∘ f) '' source.space

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}

theorem OrdinaryDoubleCurveModel.exists_component_branch_model [T2Space X]
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (i : old.Index)
    {W : Set X} (hW : IsOpen W) (hAW : f '' old.pieces i ⊆ W) :
    ∃ D : ComponentBranchModel old i, D.core ⊆ W ∧
      ∀ y, (D.charts y).source ⊆ W := by
  obtain ⟨P, hP, hPs, _⟩ := (old.models i).finitePL_id
  obtain ⟨s, F, C, K, A, H, g, B, hC, hAC, hCW, hFc, hsep, hK, hAK, hfull,
    hKs, hAs, hH, hg, hgPL, hF, hB, hstar, hraw, S, T, hSK, hSfull,
    hT, hTs, hTPL, hSs⟩ :=
    old.exists_component_axis_model_with_raw_branches hf he i P hP hPs hW hAW
  exact ⟨{
    sample := s, graph := F, core := C, complex := K, axis := A, diskImage := S,
    source := T, homeomorph := H, inverse := g, charts := B,
    core_compact := hC, core_neighborhood := hAC, graph_continuous := hFc,
    graph_separates := hsep, complex_finite := hK, axis_le := hAK, axis_full := hfull,
    complex_space := hKs, axis_space := hAs, homeomorph_value := hH,
    inverse_value := hg, inverse_PL := hgPL, selected_PL := hF,
    chart_point := fun y => (hB y).1, chart_compatible := fun y => (hB y).2.2.1,
    chart_axis := fun y => (hB y).2.2.2, raw_charts := hraw, selected_stars := hstar,
    diskImage_le := hSK, diskImage_full := hSfull, source_finite := hT,
    source_space := hTs, source_PL := hTPL, source_image := hSs }, hCW,
    fun y => (hB y).2.1⟩

theorem ComponentBranchModel.graph_inverse (D : ComponentBranchModel old i)
    (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) : D.graph (D.inverse z) = z := by
  rw [← D.homeomorph_value]
  have heq : D.inverse z = D.homeomorph.symm ⟨z, hz⟩ := Subtype.ext (D.inverse_value ⟨z, hz⟩)
  rw [heq, D.homeomorph.apply_symm_apply]

theorem ComponentBranchModel.mem_diskImage (D : ComponentBranchModel old i)
    (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) :
    z ∈ D.diskImage.space ↔ (D.inverse z : X) ∈ f '' D2 := by
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

theorem RawCrossingChart.disk_image_iff
    {x y : V2} (C : RawCrossingChart e f R x y)
    (z : X) (hz : z ∈ C.chart.source) :
    z ∈ f '' D2 ↔ z ∈ R ∧ (C.chart z 0 = 0 ∨ C.chart z 1 = 0) := by
  have h : z ∈ f '' D2 ↔ z ∈ f '' C.left ∪ f '' C.right := by
    constructor
    · rintro ⟨a, ha, haz⟩
      have ha' := C.whole_preimage.subset ⟨ha, by change f a ∈ C.chart.source; rwa [haz]⟩
      exact ha'.elim (fun hL => Or.inl ⟨a, hL, haz⟩) (fun hR => Or.inr ⟨a, hR, haz⟩)
    · rintro (⟨a, ha, haz⟩ | ⟨a, ha, haz⟩)
      · exact ⟨a, C.left_subset ha, haz⟩
      · exact ⟨a, C.right_subset ha, haz⟩
  rw [h, mem_union, C.left_image z hz, C.right_image z hz]
  tauto

theorem ComponentBranchModel.exists_raw_star (D : ComponentBranchModel old i)
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    ∃ (x y : V2) (C : RawCrossingChart e f R x y),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      ∀ z ∈ (D.complex.closedStar p).space,
        z ∈ D.diskImage.space ↔ (D.inverse z : X) ∈ R ∧
          (C.chart (D.inverse z) 0 = 0 ∨ C.chart (D.inverse z) 1 = 0) := by
  obtain ⟨q, hmap, hface⟩ := D.selected_stars p hp
  obtain ⟨x, y, C, _, hB, hBC⟩ := D.raw_charts q
  refine ⟨x, y, C, fun _ hz => hBC (hmap hz), ?_, ?_⟩
  · simpa only [hB] using hface
  · intro z hz
    rw [D.mem_diskImage z (SimplicialComplex.space_subset_of_le
      (show D.complex.closedStar p ≤ D.complex from fun _ ht => ht.1) hz)]
    exact C.disk_image_iff _ (hBC (hmap hz))

end PoincareConjecture.M76.Dehn
