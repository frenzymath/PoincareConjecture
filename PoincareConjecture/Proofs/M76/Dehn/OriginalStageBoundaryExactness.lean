import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryTopCycles
import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryEulerCounts
import PoincareConjecture.Proofs.M76.Dehn.OriginalStageTopChains
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BoundaryChainRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BoundaryExactnessRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TerminalModTwoChains

set_option autoImplicit false

universe u v w z

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U : Type u} {G : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [DecidableEq G] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Stage.relative_region_boundary_exactness (st : Stage e S f r C)
    {R : Set M} {N : Set st.Carrier} (hN : IsClosed N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    {u : U} (hu : u ∈ S.space) (hfu : f u ∈ frontier R)
    (a : C(N, N))
    (H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' (st.sourceMap '' S.space)))
    (ha : range a = Subtype.val ⁻¹' (st.sourceMap '' S.space))
    (K : SimplicialComplex ℝ G) (hK : K.faces.Finite)
    (A : SimplicialComplex ℝ G) (hAK : A ≤ K) [Fintype A.vertices]
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    (J : N ≃ₜ K.space) (F : st.Carrier → G) (g : G → N)
    (hJF : ∀ x : N, (J x : G) = F x)
    (hg : ∀ z : K.space, (g z : st.Carrier) = (J.symm z : st.Carrier))
    (hAs : A.space = F '' frontier N)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z => (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)))
    (hterminal : ∀ (Y : Type (max w v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → st.Carrier),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False) :
    let L := A.vertexAbstractComplex.toPreAbstractSimplicialComplex
    LinearMap.ker (edgeCoboundary L) = LinearMap.range (vertexCoboundary L) ∧
      LinearMap.range (edgeCoboundary L).dualMap =
        LinearMap.ker (vertexCoboundary L).dualMap := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let KL := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let AL := A.vertexAbstractComplex.toPreAbstractSimplicialComplex
  have hboundary (z : G) (hz : z ∈ K.space) :
      (g z : st.Carrier) ∈ frontier N ↔ z ∈ A.space := by
    rw [hAs]
    exact PoincareConjecture.M76.original_model_mem_image_iff J F g hJF hg
      hN.frontier_subset ⟨z, hz⟩
  have hpure := PoincareConjecture.M76.exists_tetrahedral_coface_of_original_chart_stars
    K hK J g hg hstars
  let : ConnectedSpace N := st.connectedSpace_relative_region hDN a H ha
  let : ConnectedSpace K.space := J.connectedSpace_iff.mp inferInstance
  have hconn : IsConnected K.space := isConnected_iff_connectedSpace.mpr inferInstance
  have hedge := K.connected_edgeGraph_of_isConnected hK hconn
  have htet := original_chart_stars_tetrahedron_connected
    K hK A hAK hfull hN J F g hJF hg hAs hpure hstars hconn
  have hcofaces := original_chart_stars_tetrahedron_cofaces
    K hK A hAK hfull hN J F g hJF hg hAs hpure hstars
  have hsurface := PoincareConjecture.M76.original_boundary_surface_incidence
    K A hK hAK hN.frontier_subset J g hg hboundary hstars
  have hboundaryCofaces (q : Edge AL) : (triangleCofaces AL q).card = 2 := by
    rw [A.triangleCofaces_card_eq_original q]
    let s : Finset G := q.val.map (Function.Embedding.subtype _)
    have hs : s ∈ A.faces := q.property.1
    have hsc : s.card = 2 := by
      simpa only [s, Finset.card_map] using q.property.2
    have hlink : (A.faceLink s).vertices.ncard =
        {t : Finset G | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard := by
      simpa only [hsc] using A.ncard_faceLink_vertices_eq_cofaces s
    exact hlink.symm.trans (hsurface.2.1 s hs hsc)
  have huN := st.source_mem_frontier_of_original_rim hN hDN hNR hu hfu
  have huA : F (st.sourceMap u) ∈ A.space :=
    hAs.symm ▸ mem_image_of_mem F huN
  obtain ⟨s, hs, _⟩ := SimplicialComplex.mem_space_iff.mp huA
  obtain ⟨t, ht, _, htc⟩ := hsurface.1 s hs
  let tg : Triangle A.toPreAbstractSimplicialComplex := ⟨t, ht, htc⟩
  let tv : Triangle AL := (A.vertexFaceEquiv 3).symm tg
  have hbound := K.boundary_topCycle_rank_bound A hAK hcofaces htet hboundaryCofaces tv
  have htop : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AL).dualMap) =
      Module.finrank (ZMod 2) (LinearMap.ker (vertexCoboundary AL)) :=
    (PoincareConjecture.M76.original_boundary_topCycleEquiv
      K A hK hAK hN.frontier_subset J g hg hboundary hstars).finrank_eq.symm
  have hgeometricCount := (PoincareConjecture.M76.original_chart_stars_boundary_counts
    K A hK hAK hfull hN.frontier_subset J g hg hboundary hstars).2.2.2
  have hcount : 2 * Nat.card K.vertices + 2 * Nat.card (Triangle KL) +
      Nat.card (Edge AL) = 2 * Nat.card (Edge KL) + 2 * Nat.card (Tetrahedron KL) +
        Nat.card A.vertices + Nat.card (Triangle AL) := by
    rw [Nat.card_congr (K.vertexFaceEquiv 3), Nat.card_congr (A.vertexFaceEquiv 2),
      Nat.card_congr (K.vertexFaceEquiv 2), Nat.card_congr (K.vertexFaceEquiv 4),
      Nat.card_congr (A.vertexFaceEquiv 3)]
    exact hgeometricCount
  have hend (x : st.Carrier) : st.endpoint x ∈ st.sourceMap '' S.space :=
    st.endpoint_range.subset (mem_range_self x)
  have haend (x : N) : (a x : st.Carrier) ∈ st.sourceMap '' S.space :=
    ha.subset (mem_range_self x)
  have hexactK := ker_edgeCoboundary_eq_range_vertexCoboundary KL
    K.vertexAbstractComplex.singleton_mem hDN st.deformation hend H haend
    (K.finiteBarycentricHomeomorph.trans J.symm) hterminal
  have hexact := K.vertexAbstractComplex.boundary_incidence_exact_of_counts
    A.vertexAbstractComplex hedge hexactK htop hbound hcount
  exact ⟨hexact, A.vertexAbstractComplex.boundary_chain_exact_of_incidence hexact⟩

end Geometry.OriginalPLTower
