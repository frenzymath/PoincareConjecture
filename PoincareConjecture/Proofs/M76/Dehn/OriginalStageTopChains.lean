import PoincareConjecture.Proofs.M76.Dehn.OriginalTetrahedronChains
import PoincareConjecture.Proofs.M76.Dehn.OriginalRimFrontier
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CompactTerminalCover

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U G M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [DecidableEq G] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Stage.connectedSpace_relative_region (st : Stage e S f r C)
    {N : Set st.Carrier} (hDN : st.sourceMap '' S.space ⊆ N)
    (a : C(N, N))
    (H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' (st.sourceMap '' S.space)))
    (ha : range a = Subtype.val ⁻¹' (st.sourceMap '' S.space)) : ConnectedSpace N := by
  let b : C(st.Carrier, N) := ⟨fun x =>
    ⟨st.endpoint x, hDN (st.endpoint_range.subset (mem_range_self x))⟩,
    st.endpoint.continuous.subtype_mk _⟩
  have hb : range b = Subtype.val ⁻¹' (st.sourceMap '' S.space) := by
    ext n
    constructor
    · rintro ⟨x, rfl⟩
      exact st.endpoint_range.subset (mem_range_self x)
    · intro hn
      obtain ⟨x, hx⟩ := st.endpoint_range.symm.subset hn
      exact ⟨x, Subtype.ext hx⟩
  exact H.toHomotopy.connectedSpace_of_range
    ((ha.trans hb.symm).symm ▸ isConnected_range b.continuous)

open Classical in

theorem Stage.relative_region_top_chains (st : Stage e S f r C)
    {R : Set M} {N : Set st.Carrier} (hN : IsClosed N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    {u : U} (hu : u ∈ S.space) (hfu : f u ∈ frontier R)
    (a : C(N, N))
    (H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' (st.sourceMap '' S.space)))
    (ha : range a = Subtype.val ⁻¹' (st.sourceMap '' S.space))
    (K : SimplicialComplex ℝ G) (hK : K.faces.Finite) [Fintype K.vertices]
    (L : SimplicialComplex ℝ G) (hLK : L ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ L.vertices) → s ∈ L.faces)
    (J : N ≃ₜ K.space) (F : st.Carrier → G) (g : G → N)
    (hJF : ∀ x : N, (J x : G) = F x)
    (hg : ∀ z : K.space, (g z : st.Carrier) = (J.symm z : st.Carrier))
    (hLs : L.space = F '' frontier N)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z => (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y))) :
    let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
    let B : Triangle A → Prop := fun t =>
      t.val.map (Function.Embedding.subtype _) ∈ L.faces
    (tetrahedronGraph A).Connected ∧
      (∀ c : Module.Dual (ZMod 2) (Tetrahedron A → ZMod 2),
        (∀ t : Triangle A, ¬ B t → (triangleCoboundary A).dualMap c (Pi.single t 1) = 0) →
        ∃ z : ZMod 2, c = z • totalTetrahedronChain A ∧
          (triangleCoboundary A).dualMap c = z • markedTriangleChain A B) ∧
      Function.Injective (triangleCoboundary A).dualMap := by
  let : ConnectedSpace N := st.connectedSpace_relative_region hDN a H ha
  let : ConnectedSpace K.space := J.connectedSpace_iff.mp inferInstance
  have hconn : IsConnected K.space := isConnected_iff_connectedSpace.mpr inferInstance
  have hfront : (frontier N).Nonempty :=
    ⟨st.sourceMap u, st.source_mem_frontier_of_original_rim hN hDN hNR hu hfu⟩
  exact ⟨original_chart_stars_tetrahedron_connected
    K hK L hLK hfull hN J F g hJF hg hLs hpure hstars hconn,
    fun c hc => original_chart_stars_relative_top_chain
      K hK L hLK hfull hN J F g hJF hg hLs hpure hstars hconn c hc,
    original_chart_stars_boundary3_injective
      K hK L hLK hfull hN J F g hJF hg hLs hpure hstars hconn hfront⟩

end Geometry.OriginalPLTower
