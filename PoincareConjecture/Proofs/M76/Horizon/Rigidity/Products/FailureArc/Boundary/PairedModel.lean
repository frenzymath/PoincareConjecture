import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedRimRefinement









set_option autoImplicit false
open Set Metric Geometry
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {M ι : Type} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → M}
  {r : M → ℝ} {C R : Set M} {st : Stage e S g r C}


structure MarkedBoundaryPair (st : Stage e S g r C) (R : Set M) (F : Bool → Set M) where
  model : MarkedTerminalRegion st R
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
  essential : ∀ b, ¬ (model.originalProjection.comp
    ((ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le (rim_le b))).comp
      (parametrization b : C(Q2, (rims b).space)))).Nullhomotopic
  marked : ∀ (b : Bool) (u : Q2),
    (model.originalProjection ⟨parametrization b u,
      SimplicialComplex.space_subset_of_le (rim_le b) (parametrization b u).property⟩ : M) ∈ F b

theorem MarkedTerminalRegion.nonempty_paired_boundary
    (N : MarkedTerminalRegion st R)
    (hsource : S.space = ProtectedAnnulus.source)
    (hfront : ∀ u : Q2, g (ProtectedAnnulus.endpoint false, u) ∈ frontier R)
    (hterminal : ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
      (p : Y → st.Carrier), IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
      ∀ negative : C(Q2, Y),
        (∀ u, p (negative u) = st.sourceMap (ProtectedAnnulus.endpoint false, u)) → False)
    (a : Bool → V2 → (N.sample → ℝ × V3))
    (gamma : Bool → C(Q2, N.boundary.space))
    (haPL : ∀ b, FinitePiecewiseAffineOn (a b) Q2)
    (hai : ∀ b, InjOn (a b) Q2)
    (hgamma : ∀ (b : Bool) (u : Q2), (gamma b u : N.sample → ℝ × V3) = a b u)
    (hnon : ∀ b, ¬ (N.originalProjection.comp (gamma b)).Nullhomotopic)
    (hdis : Disjoint (a false '' Q2) (a true '' Q2))
    (F : Bool → Set M)
    (hmark : ∀ (b : Bool) (u : Q2), (N.originalProjection (gamma b u) : M) ∈ F b) :
    Nonempty (MarkedBoundaryPair st R F) := by
  classical
  have haB (b : Bool) : MapsTo (a b) Q2 N.boundary.space := by
    intro u hu
    rw [← hgamma b ⟨u, hu⟩]
    exact (gamma b ⟨u, hu⟩).property
  obtain ⟨K, B, U, Q, n, P, delta, hK, hKN, hBK, hBs, hBfull,
      hUB, hUfaces, hUs, hUfull, hQdis, hQ⟩ :=
    N.complex.exists_refinement_with_paired_embedded_rims N.boundary N.finite N.boundary_le
      a haPL hai haB hdis
  let J : N.region ≃ₜ K.space :=
    N.homeomorph.trans (Homeomorph.setCongr hKN.space_eq.symm)
  have hJ (x : N.region) : (J x : N.sample → ℝ × V3) = N.graph x := N.homeomorph_value x
  have hInv (z : K.space) : (N.inverse z : st.Carrier) = (J.symm z : st.Carrier) :=
    N.inverse_value ⟨z, hKN.space_eq.subset z.property⟩
  have hboundary : B.space = N.graph '' frontier N.region := hBs.trans N.boundary_image
  have hstars : ∀ p ∈ K.vertices, ∃ T : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z ↦ (N.inverse z : st.Carrier)) (K.closedStar p).space T.source ∧
      (∀ i, (st.charts i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
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
    apply finrank_closed_le_coboundaries_add_one_of_marked_loop
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex
      K.vertexAbstractComplex.singleton_mem N.source_subset
      st.deformation (fun x ↦ st.endpoint_range.subset (mem_range_self x))
      N.deformation (fun x ↦ N.endpoint_range.subset (mem_range_self x))
      (K.finiteBarycentricHomeomorph.trans J.symm)
      (st.annulusRim hsource false)
      (fun u ↦ st.annulusRim_range_subset hsource false (mem_range_self u)) hterminal
  let u0 : Q2 := squareRimLoop 0
  have hu0 : (ProtectedAnnulus.endpoint false, (u0 : V2)) ∈ S.space :=
    hsource.symm.subset ⟨sphere_subset_closedBall
      (ProtectedAnnulus.endpoint_mem_sphere false), u0.property⟩
  have hboundaryRank := st.relative_region_boundary_first_homology_le_two
    N.compact.isClosed N.source_subset N.projection_subset hu0 (hfront u0)
    N.endpoint N.deformation N.endpoint_range K hK B hBK hBfull J N.graph N.inverse
    hJ hInv hboundary (by
      intro p hp
      obtain ⟨T, hT, _, hPL, hreg⟩ := hstars p hp
      exact ⟨T, hT, hPL, hreg⟩) hrank
  let model : MarkedTerminalRegion st R := {
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

  have hproj (b : Bool) (u : Q2) :
      model.originalProjection ⟨delta b u,
        SimplicialComplex.space_subset_of_le (hQ b).2.1 (delta b u).property⟩ =
        N.originalProjection (gamma b u) := by
    apply Subtype.ext
    change st.projection (J.symm _) = st.projection (N.homeomorph.symm _)
    apply congrArg st.projection
    apply congrArg Subtype.val
    apply N.homeomorph.injective
    apply Subtype.ext
    have hv := J.apply_symm_apply ⟨delta b u,
      SimplicialComplex.space_subset_of_le ((hQ b).2.1.trans hBK) (delta b u).property⟩
    have hv' := congrArg (fun x : K.space ↦ (x : N.sample → ℝ × V3)) hv
    change (N.homeomorph (J.symm _) : N.sample → ℝ × V3) = _ at hv'
    rw [hv']
    rw [N.homeomorph.apply_symm_apply]
    exact ((hQ b).2.2.2.2.2.2.2.2.2 u).trans (hgamma b u).symm
  refine ⟨{
    model := model
    rims := Q
    mark := U
    mark_le := hUB
    mark_faces := hUfaces
    mark_full := hUfull
    rim_le := fun b ↦ (hQ b).2.1
    disjoint := hQdis
    parametrization := delta
    parametrization_PL := fun b ↦ (hQ b).2.2.2.2.2.2.2.1
    essential := ?_
    marked := ?_ }⟩
  · intro b hn
    have heq : model.originalProjection.comp
        ((ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le (hQ b).2.1)).comp
          (delta b : C(Q2, (Q b).space))) = N.originalProjection.comp (gamma b) :=
      ContinuousMap.ext (hproj b)
    exact hnon b (heq ▸ hn)
  · intro b u
    rw [hproj]
    exact hmark b u

end Geometry.OriginalPLTower
