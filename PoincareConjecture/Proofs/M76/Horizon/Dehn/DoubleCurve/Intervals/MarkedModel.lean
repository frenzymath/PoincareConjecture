import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.PairedComponentCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.SelectedChartStars
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeModel

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

structure OrdinaryIntervalMarkedModel {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (i : old.Index) where
  mate_ne : old.mate i ≠ i
  source : Fin 3 → SimplicialComplex ℝ V2
  source_finite : ∀ j, (source j).faces.Finite
  source_subset : ∀ j, (source j).space ⊆ D2
  source_PL : ∀ j, PolyhedralPLInCharts e f (source j).space
  selected_source : (source 2).space = old.pieces i
  left_contains : old.pieces i ⊆ (source 0).space
  right_contains : old.pieces (old.mate i) ⊆ (source 1).space
  disjoint : Disjoint (source 0).space (source 1).space
  left_embedding : IsEmbedding (fun x : (source 0).space ↦ f x)
  right_embedding : IsEmbedding (fun x : (source 1).space ↦ f x)
  left_open : Set D2
  right_open : Set D2
  left_isOpen : IsOpen left_open
  right_isOpen : IsOpen right_open
  left_neighborhood : (Subtype.val : D2 → V2) ⁻¹' old.pieces i ⊆ left_open
  right_neighborhood : (Subtype.val : D2 → V2) ⁻¹' old.pieces (old.mate i) ⊆ right_open
  left_open_subset : Subtype.val '' left_open ⊆ (source 0).space
  right_open_subset : Subtype.val '' right_open ⊆ (source 1).space
  target : Set X
  target_open : IsOpen target
  target_contains : f '' old.pieces i ⊆ target
  full_preimage : ∀ x ∈ D2, f x ∈ target → x ∈ (source 0).space ∪ (source 1).space
  intersection : target ∩ (f '' (source 0).space ∩ f '' (source 1).space) = f '' old.pieces i
  charts : f '' old.pieces i → OpenPartialHomeomorph X V3
  chart_point : ∀ y, (y : X) ∈ (charts y).source
  chart_subset : ∀ y, (charts y).source ⊆ target
  chart_compatible : ∀ y k, (e k).symm.trans (charts y) ∈ piecewiseAffineGroupoid V3
  chart_left : ∀ y z, z ∈ (charts y).source →
    (z ∈ f '' (source 0).space ↔ charts y z 0 = 0 ∧ z ∈ R)
  chart_right : ∀ y z, z ∈ (charts y).source →
    (z ∈ f '' (source 1).space ↔ charts y z 1 = 0 ∧ z ∈ R)
  chart_axis : ∀ y z, z ∈ (charts y).source →
    (z ∈ f '' old.pieces i ↔ z ∈ R ∧ charts y z 0 = 0 ∧ charts y z 1 = 0)
  chart_region : ∀ y, (charts y).source ⊆ interior R ∨
    ((∀ z ∈ (charts y).source, z ∈ R ↔ 0 ≤ charts y z 2) ∧
      ∀ z ∈ (charts y).source, z ∈ frontier R ↔ charts y z 2 = 0)
  sample : Finset (f '' old.pieces i)
  graph : X → (sample → ℝ × V3)
  core : Set X
  complex : SimplicialComplex ℝ (sample → ℝ × V3)
  marks : Sum Bool (Fin 3) → SimplicialComplex ℝ (sample → ℝ × V3)
  homeomorph : core ≃ₜ complex.space
  inverse : (sample → ℝ × V3) → core
  clips : Fin 3 → SimplicialComplex ℝ V2
  core_compact : IsCompact core
  core_neighborhood : f '' old.pieces i ⊆ interior core
  core_subset : core ⊆ target
  graph_continuous : Continuous graph
  graph_PL : ∀ k, LocallyPiecewiseAffineOn (graph ∘ (e k).symm) (e k).target
  graph_separates : ∀ x ∈ core, ∀ y : X, graph x = graph y → x = y
  complex_finite : complex.faces.Finite
  marks_full : ∀ j, marks j ≤ complex ∧ (marks j).faces.Finite ∧
    ∀ t ∈ complex.faces, (∀ v ∈ t, v ∈ (marks j).vertices) → t ∈ (marks j).faces
  complex_image : complex.space = graph '' core
  region_image : (marks (.inl false)).space = graph '' (core ∩ R)
  frontier_image : (marks (.inl true)).space = graph '' (core ∩ frontier R)
  marks_image : ∀ j, (marks (.inr j)).space = graph '' (core ∩ (f '' (source j).space))
  clips_data : ∀ j, (clips j).faces.Finite ∧
    (clips j).space = (source j).space ∩ f ⁻¹' core ∧
    FinitePiecewiseAffineOn (graph ∘ f) (clips j).space ∧
    (graph ∘ f) '' (clips j).space = (marks (.inr j)).space
  homeomorph_value : ∀ x : core, (homeomorph x : sample → ℝ × V3) = graph x
  inverse_continuous : ContinuousOn inverse complex.space
  inverse_value : ∀ z : complex.space, (inverse z : X) = (homeomorph.symm z : X)
  inverse_PL : PolyhedralPLInCharts e (fun z ↦ (inverse z : X)) complex.space
  local_projections : ∀ x ∈ core, ∃ (k : ι) (V : Set X)
    (a : (sample → ℝ × V3) →ᴬ[ℝ] V3),
    IsOpen V ∧ x ∈ V ∧ V ⊆ (e k).source ∧ EqOn (a ∘ graph) (e k) V
  selected_stars : ∀ p ∈ (marks (.inr 2)).vertices,
    ∃ y : f '' old.pieces i,
      MapsTo (fun z ↦ (inverse z : X)) (complex.closedStar p).space (charts y).source ∧
      (complex.closedStar p).AffineOnFaces (charts y ∘ (fun z ↦ (inverse z : X)))

theorem OrdinaryDoubleCurveModel.nonempty_interval_marked_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (i : old.Index)
    (hball : IsFinitePLBallPair ℝ (old.pieces i) (old.pieces i ∩ Q2))
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2) :
    Nonempty (OrdinaryIntervalMarkedModel old i) := by
  classical
  have hne := (old.exists_interval_arc_parameters hf hin hfront i hball).1
  obtain ⟨P, Q, U, V, O, B, hP, hQ, hPD, hQD, hPQ, hU, hV,
      hiU, hmV, hUP, hVQ, hiP, hmQ, hPi, hQi, hPPL, hQPL,
      hO, hAO, hfull, hinter, hB⟩ := old.exists_paired_component_charts hf i hne
  have htri : ∃ S : SimplicialComplex ℝ V2, S.faces.Finite ∧ S.space = old.pieces i := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨S, hS, hSs, _⟩, _⟩, _⟩ := hball
    exact ⟨S, hS, hSs⟩
  obtain ⟨S, hS, hSs⟩ := htri
  let source : Fin 3 → SimplicialComplex ℝ V2 := ![P, Q, S]
  have hsource : ∀ j, (source j).faces.Finite := by
    intro j
    fin_cases j <;> assumption
  have hSD : S.space ⊆ D2 := fun x hx ↦ (old.piece_subset_double i (hSs ▸ hx)).1
  have hsourceD : ∀ j, (source j).space ⊆ D2 := by
    intro j
    fin_cases j <;> assumption
  have hSPL := hf.restrict_finite S hS hSD
  have hsourcePL : ∀ j, PolyhedralPLInCharts e f (source j).space := by
    intro j
    fin_cases j <;> assumption
  have hAc : IsCompact (f '' old.pieces i) :=
    (old.compact i).image_of_continuousOn
      (hf.continuousOn.mono (fun x hx ↦ (old.piece_subset_double i hx).1))
  have hAn : (f '' old.pieces i).Nonempty := (old.connected i).nonempty.image f
  obtain ⟨s, F, C, K0, J, H0, g, T, hC, hAC, hCO, hFc, hFPL, hsep, hK0,
      hJ, hK0s, hJR, hJF, hJimage, hT, hH0, hgc, hg, hgPL, hproj⟩ :=
    exists_original_signed_tube_model he hAc hAn hO hAO (fun _ : Fin 3 ↦ V2)
      source hsource (fun _ ↦ f) hsourcePL
  have htrace (Z : Set X) :
      K0.space ∩ (fun z ↦ (g z : X)) ⁻¹' Z = F '' (C ∩ Z) := by
    ext z
    constructor
    · rintro ⟨hz, hgz⟩
      refine ⟨g z, ⟨(g z).property, hgz⟩, ?_⟩
      exact (congrArg F (hg ⟨z, hz⟩)).trans ((hH0 (H0.symm ⟨z, hz⟩)).symm.trans
        (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz⟩)))
    · rintro ⟨x, hx, rfl⟩
      have hxK : F x ∈ K0.space := hK0s.symm ▸ mem_image_of_mem F hx.1
      refine ⟨hxK, ?_⟩
      have hv : (g (F x) : X) = x := by
        simpa only [hH0, H0.symm_apply_apply] using hg (H0 ⟨x, hx.1⟩)
      change (g (F x) : X) ∈ Z
      rw [hv]
      exact hx.2
  let G (q : (K0.space ∩ (fun z ↦ (g z : X)) ⁻¹' (f '' old.pieces i) : Set _)) :=
    B ⟨g q, q.property.2⟩
  have hJa : (J (.inr 2)).space =
      K0.space ∩ (fun z ↦ (g z : X)) ⁻¹' (f '' old.pieces i) := by
    rw [hJimage, htrace]
    change F '' (C ∩ (f '' S.space)) = _
    rw [hSs]
  have hJK (j : Sum Bool (Fin 3)) : (J j).space ⊆ K0.space := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := SimplicialComplex.mem_space_iff.mp hz
    exact K0.convexHull_subset_space ((hJ j).1 ht) hzt
  obtain ⟨K, L, hK, hKK0, hL, hstars⟩ := exists_selected_compatible_chart_stars
    e he.compatible he.cover K0 hK0 hgPL hAc.isClosed G
      (fun q k ↦ (hB ⟨g q, q.property.2⟩).2.2.1 k)
      (fun q ↦ (hB ⟨g q, q.property.2⟩).1)
      J (fun j ↦ (hJ j).2.1) hJK (.inr 2) hJa
  let H : C ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  refine ⟨{
    mate_ne := hne
    source := source
    source_finite := hsource
    source_subset := hsourceD
    source_PL := hsourcePL
    selected_source := hSs
    left_contains := hiP
    right_contains := hmQ
    disjoint := hPQ
    left_embedding := hPi
    right_embedding := hQi
    left_open := U
    right_open := V
    left_isOpen := hU
    right_isOpen := hV
    left_neighborhood := hiU
    right_neighborhood := hmV
    left_open_subset := hUP
    right_open_subset := hVQ
    target := O
    target_open := hO
    target_contains := hAO
    full_preimage := hfull
    intersection := hinter
    charts := B
    chart_point := fun y ↦ (hB y).1
    chart_subset := fun y ↦ (hB y).2.1
    chart_compatible := fun y ↦ (hB y).2.2.1
    chart_left := fun y ↦ (hB y).2.2.2.1
    chart_right := fun y ↦ (hB y).2.2.2.2.1
    chart_axis := fun y ↦ (hB y).2.2.2.2.2.1
    chart_region := fun y ↦ (hB y).2.2.2.2.2.2
    sample := s
    graph := F
    core := C
    complex := K
    marks := L
    homeomorph := H
    inverse := g
    clips := T
    core_compact := hC
    core_neighborhood := hAC
    core_subset := hCO
    graph_continuous := hFc
    graph_PL := hFPL
    graph_separates := hsep
    complex_finite := hK
    marks_full := fun j ↦ ⟨(hL j).1, hK.subset (hL j).1, (hL j).2.2⟩
    complex_image := hKK0.space_eq.trans hK0s
    region_image := (hL (.inl false)).2.1.trans hJR
    frontier_image := (hL (.inl true)).2.1.trans hJF
    marks_image := fun j ↦ (hL (.inr j)).2.1.trans (hJimage j)
    clips_data := fun j ↦ ⟨(hT j).1, (hT j).2.1, (hT j).2.2.1,
      (hT j).2.2.2.trans (hL (.inr j)).2.1.symm⟩
    homeomorph_value := hH0
    inverse_continuous := hKK0.space_eq.symm ▸ hgc
    inverse_value := fun z ↦ hg ⟨z, hKK0.space_eq.subset z.property⟩
    inverse_PL := hKK0.space_eq.symm ▸ hgPL
    local_projections := hproj
    selected_stars := ?_
  }⟩
  intro p hp
  obtain ⟨q, hq⟩ := hstars p hp
  exact ⟨⟨g q, q.property.2⟩, hq⟩

end PoincareConjecture.M76.Dehn
