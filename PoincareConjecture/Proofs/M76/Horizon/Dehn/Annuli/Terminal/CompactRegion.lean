import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.OriginalMarkedRanks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Boundary.OriginalRegionRanks
import PoincareConjecture.Proofs.M76.Dehn.OriginalStageNeighborhood
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Dehn.FullMarkedTerminalStars









set_option autoImplicit false

universe w z

open Set Metric Geometry
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {M : Type w} {ι : Type z} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → M}
  {r : M → ℝ} {C : Set M}



structure MarkedTerminalRegion (st : Stage e S f r C) (R : Set M) where
  region : Set st.Carrier
  compact : IsCompact region
  domain : PLDomain st.charts region
  source_subset : st.sourceMap '' S.space ⊆ region
  projection_subset : region ⊆ st.projection ⁻¹' R
  source_frontier : ∀ u ∈ S.space, f u ∈ frontier R → st.sourceMap u ∈ frontier region
  endpoint : C(region, region)
  deformation : (ContinuousMap.id region).HomotopyRel endpoint
    (Subtype.val ⁻¹' (st.sourceMap '' S.space))
  endpoint_range : range endpoint = Subtype.val ⁻¹' (st.sourceMap '' S.space)
  sample : Finset region
  graph : st.Carrier → (sample → ℝ × V3)
  graph_continuous : Continuous graph
  graph_PL : ∀ i, LocallyPiecewiseAffineOn (graph ∘ (st.charts i).symm) (st.charts i).target
  complex : SimplicialComplex ℝ (sample → ℝ × V3)
  boundary : SimplicialComplex ℝ (sample → ℝ × V3)
  finite : complex.faces.Finite
  boundary_le : boundary ≤ complex
  boundary_full : ∀ s ∈ complex.faces,
    (∀ v ∈ s, v ∈ boundary.vertices) → s ∈ boundary.faces
  image : complex.space = graph '' region
  boundary_image : boundary.space = graph '' frontier region
  homeomorph : region ≃ₜ complex.space
  homeomorph_value : ∀ x : region, (homeomorph x : sample → ℝ × V3) = graph x
  inverse : (sample → ℝ × V3) → region
  inverse_value : ∀ x : complex.space, (inverse x : st.Carrier) = (homeomorph.symm x : st.Carrier)
  inverse_PL : PolyhedralPLInCharts st.charts (fun z => (inverse z : st.Carrier)) complex.space
  stars : ∀ p ∈ complex.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
    MapsTo (fun z => (inverse z : st.Carrier)) (complex.closedStar p).space B.source ∧
    (∀ i, (st.charts i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
    (complex.closedStar p).AffineOnFaces (fun z => B (inverse z)) ∧
    (B.source ⊆ region ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ region ↔ 0 ≤ ell (B y))
  region_rank :
    letI : Fintype complex.vertices := (complex.finite_vertices_of_finite_faces finite).fintype
    let A := complex.vertexAbstractComplex.toPreAbstractSimplicialComplex
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary A)) + 1
  boundary_rank :
    letI : Fintype boundary.vertices :=
      (boundary.finite_vertices_of_finite_faces (finite.subset boundary_le)).fintype
    let A := boundary.vertexAbstractComplex.toPreAbstractSimplicialComplex
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A)) ≤
        Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary A)) + 2 ∧
      Module.finrank (ZMod 2) (LinearMap.ker (vertexCoboundary A).dualMap) ≤
        Module.finrank (ZMod 2) (LinearMap.range (edgeCoboundary A).dualMap) + 2 ∧
      Module.finrank (ZMod 2)
        (Submodule.Subquotient (LinearMap.ker (vertexCoboundary A).dualMap)
          (LinearMap.range (edgeCoboundary A).dualMap)) ≤ 2



theorem Stage.nonempty_marked_terminal_region (st : Stage e S f r C)
    (hS : S.faces.Finite) (hsource : S.space = ProtectedAnnulus.source)
    {R : Set M} (hfR : MapsTo f S.space R) (hR : IsClosed R)
    (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target)
    (hcut : ∀ x ∈ C, x ∈ R ↔ 0 ≤ r x)
    (hzero : ∀ x ∈ C, x ∈ frontier R ↔ r x = 0)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph M V3),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))
    (hinj : Function.Injective (fun u : Q2 => f (ProtectedAnnulus.endpoint false, u)))
    (hfront : ∀ u : Q2, f (ProtectedAnnulus.endpoint false, u) ∈ frontier R)
    (hterminal : ∀ (Y : Type w) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
      (p : Y → st.Carrier), IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
      ∀ negative : C(Q2, Y),
        (∀ u, p (negative u) = st.sourceMap (ProtectedAnnulus.endpoint false, u)) → False) :
    Nonempty (MarkedTerminalRegion st R) := by
  classical
  obtain ⟨z, c, _, _, _, _, hN, _, hDN, hdeform, hNfront, _⟩ :=
    st.exists_compact_relative_neighborhood hS hfR hR hr hrPL hcut hzero hboundary
  let N : Set st.Carrier := {x | st.projection x ∈ R ∧ c ≤ z x}
  have hNR : N ⊆ st.projection ⁻¹' R := fun _ hx => hx.1
  obtain ⟨a, H, ha, _⟩ := hdeform
  have heN : PLDomain st.charts N := ⟨st.cover, st.compatible, hN.isClosed, hNfront⟩
  obtain ⟨p, F, K0, A0, J0, hFc, hFPL, hK0, hA0, _, hK0s, hA0s, hJ0, _, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair
      st.charts st.compatible st.cover hN hNfront
  let u0 : Q2 := squareRimLoop 0
  let v0 : S.space := ⟨(ProtectedAnnulus.endpoint false, u0), hsource.symm.subset
    ⟨sphere_subset_closedBall (ProtectedAnnulus.endpoint_mem_sphere false), u0.property⟩⟩
  obtain ⟨K, A, J, g, hK, _, hA, hKs, hAs, _, hJF, _, hg, hgPL, hstars, _⟩ :=
    exists_full_marked_pair_chart_stars heN S hS st.sourcePL v0
      (image_subset_iff.mp hDN) F hFPL K0 A0 hK0 hA0 hK0s hA0s J0 hJ0 hproj
  obtain ⟨K', B, hK', J', hsub, hBK', hBs, hBfull, hJ', hg', hstars', hrank⟩ :=
    st.exists_marked_terminal_rank_refinement hsource hinj hDN H
      (fun y => ha.subset (mem_range_self y)) K (A 0) hK (hA 0).1 J F g hJF hg hFPL
      (by
        intro p hp
        obtain ⟨B, hB, hcompat, hAff, hreg⟩ := hstars p hp
        exact ⟨B, hB, hAff, hcompat, hreg⟩) hterminal
  let : Fintype K'.vertices := (K'.finite_vertices_of_finite_faces hK').fintype
  let : Fintype B.vertices := (B.finite_vertices_of_finite_faces (hK'.subset hBK')).fintype
  have hBimage : B.space = F '' frontier N := hBs.trans hAs
  have hboundaryRank := st.relative_region_boundary_first_homology_le_two
    hN.isClosed hDN hNR v0.property (hfront u0) a H ha
    K' hK' B hBK' hBfull J' F g hJ' hg' hBimage
    (by
      intro p hp
      obtain ⟨B, hB, hAff, _, hreg⟩ := hstars' p hp
      exact ⟨B, hB, hAff, hreg⟩) hrank
  exact ⟨{
    region := N
    compact := hN
    domain := heN
    source_subset := hDN
    projection_subset := hNR
    source_frontier := fun u hu hfu =>
      st.source_mem_frontier_of_original_rim hN.isClosed hDN hNR hu hfu
    endpoint := a
    deformation := H
    endpoint_range := ha
    sample := p
    graph := F
    graph_continuous := hFc
    graph_PL := hFPL
    complex := K'
    boundary := B
    finite := hK'
    boundary_le := hBK'
    boundary_full := hBfull
    image := hsub.space_eq.trans hKs
    boundary_image := hBimage
    homeomorph := J'
    homeomorph_value := hJ'
    inverse := g
    inverse_value := hg'
    inverse_PL := hsub.space_eq.symm ▸ hgPL
    stars := fun p hp => by
      obtain ⟨B, hB, hAff, hcompat, hreg⟩ := hstars' p hp
      exact ⟨B, hB, hcompat, hAff, hreg⟩
    region_rank := hrank
    boundary_rank := hboundaryRank }⟩

end Geometry.OriginalPLTower
