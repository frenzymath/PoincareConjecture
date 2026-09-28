import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.MarkedModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.ModelArc
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.PairedParameters

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_paired_marked_model_in_open
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (i : old.Index) (hi : old.mate i ≠ i)
    (S : SimplicialComplex ℝ V2) (hS : S.faces.Finite) (hSs : S.space = old.pieces i)
    {W : Set X} (hW : IsOpen W) (hAW : f '' old.pieces i ⊆ W) :
    ∃ D : OrdinaryIntervalMarkedModel old i, D.target ⊆ W := by
  classical
  obtain ⟨P, Q, U, V, O₀, B₀, hP, hQ, hPD, hQD, hPQ, hU, hV,
      hiU, hmV, hUP, hVQ, hiP, hmQ, hPi, hQi, hPPL, hQPL,
      hO₀, hAO₀, hfull₀, hinter₀, hB₀⟩ := old.exists_paired_component_charts hf i hi
  let O := O₀ ∩ W
  let B (y : f '' old.pieces i) := (B₀ y).restrOpen W hW
  have hO : IsOpen O := hO₀.inter hW
  have hAO : f '' old.pieces i ⊆ O := fun y hy ↦ ⟨hAO₀ hy, hAW hy⟩
  have hfull (x : V2) (hx : x ∈ D2) (hfx : f x ∈ O) :
      x ∈ P.space ∪ Q.space := hfull₀ x hx hfx.1
  have hinter : O ∩ (f '' P.space ∩ f '' Q.space) = f '' old.pieces i := by
    apply Subset.antisymm
    · intro y hy
      exact hinter₀.subset ⟨hy.1.1, hy.2⟩
    · intro y hy
      exact ⟨hAO hy, (hinter₀.symm.subset hy).2⟩
  have hB (y : f '' old.pieces i) :
      (y : X) ∈ (B y).source ∧ (B y).source ⊆ O ∧
      (∀ k, (e k).symm.trans (B y) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ z ∈ (B y).source, z ∈ f '' P.space ↔ B y z 0 = 0 ∧ z ∈ R) ∧
      (∀ z ∈ (B y).source, z ∈ f '' Q.space ↔ B y z 1 = 0 ∧ z ∈ R) ∧
      (∀ z ∈ (B y).source,
        z ∈ f '' old.pieces i ↔ z ∈ R ∧ B y z 0 = 0 ∧ B y z 1 = 0) ∧
      ((B y).source ⊆ interior R ∨
        ((∀ z ∈ (B y).source, z ∈ R ↔ 0 ≤ B y z 2) ∧
          ∀ z ∈ (B y).source, z ∈ frontier R ↔ B y z 2 = 0)) := by
    refine ⟨⟨(hB₀ y).1, hAW y.property⟩,
      fun z hz ↦ ⟨(hB₀ y).2.1 hz.1, hz.2⟩, ?_,
      fun z hz ↦ (hB₀ y).2.2.2.1 z hz.1,
      fun z hz ↦ (hB₀ y).2.2.2.2.1 z hz.1,
      fun z hz ↦ (hB₀ y).2.2.2.2.2.1 z hz.1, ?_⟩
    · intro k
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp ((hB₀ y).2.2.1 k)).mono
        ((e k).symm.trans (B y)).open_source (fun z hz ↦ ⟨hz.1, hz.2.1⟩)
    · rcases (hB₀ y).2.2.2.2.2.2 with hin | ⟨hr, hfr⟩
      · exact Or.inl (fun z hz ↦ hin hz.1)
      · exact Or.inr ⟨fun z hz ↦ hr z hz.1, fun z hz ↦ hfr z hz.1⟩
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
    mate_ne := hi
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
  }, fun _ hz ↦ hz.2⟩
  intro p hp
  obtain ⟨q, hq⟩ := hstars p hp
  exact ⟨⟨g q, q.property.2⟩, hq⟩

theorem OrdinaryDoubleCurveModel.exists_paired_circle_marked_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (hin : MapsTo f D2 R)
    (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : old.Index) (hi : old.mate i ≠ i)
    {n : ℕ} (P : Polygon V2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i)
    (hQ : Disjoint (old.pieces i) Q2) :
    ∃ (D : OrdinaryIntervalMarkedModel old i) (a : Q2 ≃ₜ old.pieces i),
      a.IsFinitePL ∧ D.target ⊆ interior R ∧ D.core ⊆ interior R ∧
      (∀ y, (D.charts y).source ⊆ interior R) ∧
      (D.source 2).space = P.boundary ℝ ∧ (D.clips 2).space = P.boundary ℝ ∧
      (D.marks (.inr 2)).space = (D.graph ∘ f) '' P.boundary ℝ ∧
      (D.marks (.inl true)).space = ∅ ∧
      (D.marks (.inl false)).space = D.complex.space ∧
      D2 ∩ f ⁻¹' D.core = (D.clips 0).space ∪ (D.clips 1).space := by
  obtain ⟨a, _, circle, ha, _, _, _, _, _, himage, hinside, _⟩ :=
    old.exists_paired_circle_parameters hf hin hfront i hi P hP hPi hPs hQ
  have hAin : f '' old.pieces i ⊆ interior R := by
    rw [← himage]
    rintro _ ⟨x, hx, rfl⟩
    exact hinside hx
  obtain ⟨D, htarget⟩ := old.exists_paired_marked_model_in_open hf he i hi
    (P.simplicialComplex hP) (P.finite_simplicialComplex_faces hP)
    ((P.simplicialComplex_space hP).trans hPs) isOpen_interior hAin
  have hcore : D.core ⊆ interior R := D.core_subset.trans htarget
  have hselected : (D.marks (.inr 2)).space = (D.graph ∘ f) '' P.boundary ℝ := by
    rw [← (D.clips_data 2).2.2.2, D.selected_clip, hPs]
  have hfrontier : (D.marks (.inl true)).space = ∅ := by
    rw [D.frontier_image]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨x, hx, _⟩
    exact disjoint_left.mp disjoint_interior_frontier (hcore hx.1) hx.2
  have hregion : (D.marks (.inl false)).space = D.complex.space := by
    rw [D.region_image, D.complex_image,
      inter_eq_left.mpr (hcore.trans interior_subset)]
  refine ⟨D, a, ha, htarget, hcore, fun y ↦ (D.chart_subset y).trans htarget,
    D.selected_source.trans hPs.symm, D.selected_clip.trans hPs.symm,
    hselected, hfrontier, hregion, ?_⟩
  rw [(D.clips_data 0).2.1, (D.clips_data 1).2.1]
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    rcases D.full_preimage x hx (D.core_subset hfx) with h0 | h1
    · exact Or.inl ⟨h0, hfx⟩
    · exact Or.inr ⟨h1, hfx⟩
  · rintro (h0 | h1)
    · exact ⟨D.source_subset 0 h0.1, h0.2⟩
    · exact ⟨D.source_subset 1 h1.1, h1.2⟩

end PoincareConjecture.M76.Dehn
