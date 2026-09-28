import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.OriginalRimGraphs
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedRimRefinement

set_option autoImplicit false
open Set Metric Geometry
open Geometry.OriginalPLTower
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)

structure PairedMarkedBoundary (d : ProtectedAnnulusTerminalData L retained) where
  model : MarkedTerminalRegion d.stage (chartDomain L retained)
  rims : Bool → SimplicialComplex ℝ (model.sample → ℝ × V3)
  mark : SimplicialComplex ℝ (model.sample → ℝ × V3)
  mark_le : mark ≤ model.boundary
  mark_faces : mark.faces = (rims false).faces ∪ (rims true).faces
  mark_full : ∀ s ∈ model.complex.faces,
    (∀ v ∈ s, v ∈ mark.vertices) → s ∈ mark.faces
  rim_le : ∀ b, rims b ≤ model.boundary
  disjoint : Disjoint (rims false).space (rims true).space
  parametrization : ∀ b, Q2 ≃ₜ (rims b).space
  parametrization_PL : ∀ b, (parametrization b).IsFinitePL
  parametrization_value : ∀ (b : Bool) (u : Q2),
    (parametrization b u : model.sample → ℝ × V3) =
      model.graph (d.stage.annulusRim d.source_space b u)

theorem nonempty_paired_marked_boundary (d : ProtectedAnnulusTerminalData L retained)
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source) :
    Nonempty (PairedMarkedBoundary L retained d) := by
  classical
  let N := d.compact_region
  let g := fun b ↦ N.graph ∘ d.stage.annulusRimMap b
  obtain ⟨hgPL, hgi, hgB, hgdis⟩ := original_terminal_rim_graphs L retained d hsource
  obtain ⟨K, B, U, Q, n, P, gamma, hK, hKN, hBK, hBs, hBfull,
      hUB, hUfaces, hUs, hUfull, hQdis, hQ⟩ :=
    N.complex.exists_refinement_with_paired_embedded_rims N.boundary N.finite N.boundary_le
      g hgPL hgi hgB hgdis
  let J : N.region ≃ₜ K.space :=
    N.homeomorph.trans (Homeomorph.setCongr hKN.space_eq.symm)
  have hJ (x : N.region) : (J x : N.sample → ℝ × V3) = N.graph x := N.homeomorph_value x
  have hInv (z : K.space) : (N.inverse z : d.stage.Carrier) = (J.symm z : d.stage.Carrier) :=
    N.inverse_value ⟨z, hKN.space_eq.subset z.property⟩
  have hboundary : B.space = N.graph '' frontier N.region := hBs.trans N.boundary_image
  have hstars : ∀ p ∈ K.vertices, ∃ T : OpenPartialHomeomorph d.stage.Carrier V3,
      MapsTo (fun z ↦ (N.inverse z : d.stage.Carrier)) (K.closedStar p).space T.source ∧
      (∀ i, (d.stage.charts i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (fun z ↦ T (N.inverse z)) ∧
      (T.source ⊆ N.region ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ T.source, y ∈ N.region ↔ 0 ≤ ell (T y)) := by
    intro p hp
    obtain ⟨v, hv, hsub, hAff⟩ := hKN.exists_original_affine_vertex_star (F := V3) N.finite hp
    obtain ⟨T, hT, hcompat, hPL, hreg⟩ := N.stars v hv
    exact ⟨T, hT.mono_left hsub, hcompat, hAff _ hPL, hreg⟩
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let : Fintype B.vertices := (B.finite_vertices_of_finite_faces (hK.subset hBK)).fintype
  have hQK (b : Bool) : Q b ≤ K := (hQ b).2.1.trans hBK
  let : Fintype (Q false).vertices :=
    ((Q false).finite_vertices_of_finite_faces (hK.subset (hQK false))).fintype
  have hrank : Module.finrank (ZMod 2)
      (LinearMap.ker (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (vertexCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) + 1 := by
    have hq := hQ false
    apply K.finrank_closed_le_coboundaries_add_one_of_marked_polygon (Q false)
      (hK.subset (hQK false)) (hQK false) (P false)
      hq.2.2.2.2.1 hq.2.2.2.2.2.1 hq.2.2.2.2.2.2.1 N.source_subset
      d.stage.deformation (fun x ↦ d.stage.endpoint_range.subset (mem_range_self x))
      N.deformation (fun x ↦ N.endpoint_range.subset (mem_range_self x)) J
      (d.stage.annulusRim d.source_space false)
      (fun u ↦ d.stage.annulusRim_range_subset d.source_space false (mem_range_self u))
      ?_ d.terminal
    intro u
    rw [hJ, hq.2.2.1]
    exact ⟨u, u.property, rfl⟩
  let u0 : Q2 := squareRimLoop 0
  have hu0 : (endpoint false, (u0 : V2)) ∈ d.source_complex.space :=
    d.source_space.symm.subset ⟨sphere_subset_closedBall (endpoint_mem_sphere false), u0.property⟩
  have hfront : d.map (endpoint false, (u0 : V2)) ∈ frontier (chartDomain L retained) :=
    (d.frontier_iff ⟨(endpoint false, u0),
      sphere_subset_closedBall (endpoint_mem_sphere false), u0.property⟩).mpr
        (endpoint_mem_sphere false)
  have hboundaryRank := d.stage.relative_region_boundary_first_homology_le_two
    N.compact.isClosed N.source_subset N.projection_subset hu0 hfront
    N.endpoint N.deformation N.endpoint_range K hK B hBK hBfull J N.graph N.inverse
    hJ hInv hboundary (by
      intro p hp
      obtain ⟨T, hT, _, hPL, hreg⟩ := hstars p hp
      exact ⟨T, hT, hPL, hreg⟩) hrank
  let model : MarkedTerminalRegion d.stage (chartDomain L retained) := {
    N with
    complex := K
    boundary := B
    finite := hK
    boundary_le := hBK
    boundary_full := hBfull
    image := hKN.space_eq.trans N.image
    boundary_image := hboundary
    homeomorph := J
    homeomorph_value := hJ
    inverse_value := hInv
    inverse_PL := hKN.space_eq.symm ▸ N.inverse_PL
    stars := hstars
    region_rank := hrank
    boundary_rank := hboundaryRank }
  exact ⟨{
    model := model
    rims := Q
    mark := U
    mark_le := hUB
    mark_faces := hUfaces
    mark_full := hUfull
    rim_le := fun b ↦ (hQ b).2.1
    disjoint := hQdis
    parametrization := gamma
    parametrization_PL := fun b ↦ (hQ b).2.2.2.2.2.2.2.1
    parametrization_value := fun b u ↦ (hQ b).2.2.2.2.2.2.2.2.2 u }⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
