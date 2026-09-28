import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalRanks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.CompactRegion









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



theorem Stage.nonempty_terminal_region_of_marked_loop
    {M : Type w} {ι : Type z} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3}
    {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → M}
    {r : M → ℝ} {C : Set M}
    (st : Stage e S f r C)
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
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let : Fintype (A 0).vertices :=
    ((A 0).finite_vertices_of_finite_faces (hK.subset (hA 0).1)).fintype
  have hrank :
      Module.finrank (ZMod 2)
          (LinearMap.ker (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) ≤
        Module.finrank (ZMod 2) (LinearMap.range
          (vertexCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) + 1 := by
    apply finrank_closed_le_coboundaries_add_one_of_marked_loop
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex
      K.vertexAbstractComplex.singleton_mem
      hDN st.deformation (fun x => st.endpoint_range.subset (mem_range_self x)) H
      (fun y => ha.subset (mem_range_self y)) (K.finiteBarycentricHomeomorph.trans J.symm)
      (st.annulusRim hsource false)
      (fun u => st.annulusRim_range_subset hsource false (mem_range_self u)) hterminal
  have hboundaryRank := st.relative_region_boundary_first_homology_le_two
    hN.isClosed hDN hNR v0.property (hfront u0) a H ha
    K hK (A 0) (hA 0).1 (hA 0).2.2 J F g hJF hg hAs
    (by
      intro p hp
      obtain ⟨B, hB, _, hAff, hreg⟩ := hstars p hp
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
    complex := K
    boundary := A 0
    finite := hK
    boundary_le := (hA 0).1
    boundary_full := (hA 0).2.2
    image := hKs
    boundary_image := hAs
    homeomorph := J
    homeomorph_value := hJF
    inverse := g
    inverse_value := hg
    inverse_PL := hgPL
    stars := hstars
    region_rank := hrank
    boundary_rank := hboundaryRank }⟩

end Geometry.OriginalPLTower
