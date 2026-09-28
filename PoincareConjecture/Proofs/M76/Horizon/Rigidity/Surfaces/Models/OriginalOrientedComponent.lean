import PoincareConjecture.Proofs.M76.Wall.OriginalNewFrontierModels
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalOrientation

set_option autoImplicit false

open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

open Classical in
theorem PLDomain.exists_original_oriented_component
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N)
    (x : X0) (hx : x ∈ frontier N) :
    ∃ (s : Finset N) (phi : X0 → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X0)
      (H : J.space ≃ₜ connectedComponentIn (frontier N) x),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ IsConnected J.space ∧
      (∀ t ∈ J.faces, ∃ u ∈ J.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ J.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ J.vertices, IsConnected (J.faceLink {p}).space) ∧
      PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, (H z : X0) = g z) ∧
      (∀ z ∈ J.space, phi (g z) = z) ∧
      ∃ (number : J.vertices ↪ ℕ)
        (sigma : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
        ∀ t u : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          t ≠ u → ∀ a : Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          a.val ⊆ t.val → a.val ⊆ u.val →
          (sigma t + boundaryFaceParity number t.val a.val) +
            (sigma u + boundaryFaceParity number u.val a.val) = 1 := by
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  have hNne : N.Nonempty := ⟨x, he.closed.frontier_subset hx⟩
  obtain ⟨s, phi, K, A, H, g, HB, n, pick, S,
      hphi, hphiPL, hK, hAK, hA, _, _, _, hH, hgc, hg, hgPL, hHB, _, hboundary,
      hstars, hpure, hcofaces, hlinks, hn, hS, hwhole, hdisjoint, hcomponents, hsphere⟩ :=
    he.exists_new_frontier_component_models hN hNne isClosed_empty isClosed_frontier
      (by simp) (empty_union _).symm ⟨x, hx⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hwhole.symm ▸ hx)
  have hSi : S i = connectedComponentIn (frontier N) x :=
    ((hcomponents i).2.2.2.1 x hi).symm
  let J := A.edgeComponentComplex (pick i)
  have hJA : J ≤ A := A.edgeComponentComplex_le (pick i)
  have hJK : J ≤ K := hJA.trans hAK
  have hJ : J.faces.Finite := hA.subset hJA
  have hJS : J.space ⊆ K.space := SimplicialComplex.space_subset_of_le hJK
  have hgi : InjOn (fun z ↦ (g z : X0)) K.space := by
    intro u hu v hv huv
    have hh : H.symm ⟨u, hu⟩ = H.symm ⟨v, hv⟩ :=
      Subtype.ext ((hg ⟨u, hu⟩).symm.trans (huv.trans (hg ⟨v, hv⟩)))
    exact congrArg Subtype.val (H.symm.injective hh)
  have hfront : MapsTo (fun z ↦ (g z : X0)) J.space (frontier N) := by
    intro z hz
    exact (hboundary z (hJS hz)).mpr (SimplicialComplex.space_subset_of_le hJA hz)
  obtain ⟨number, sigma, hcancel⟩ := exists_hamiltonZero_frontier_all_edge_signs
    e hcover hcompat K J hJK hJ (fun z ↦ (g z : X0)) N hgi
    (hgPL.continuousOn.mono hJS) hfront hstars
  obtain ⟨HC, hHC⟩ := (hcomponents i).2.2.2.2.2
  refine ⟨s, phi, J, fun z ↦ g z, HC.trans (Homeomorph.setCongr hSi),
    hphi, hphiPL, hJ, (A.edgeComponentComplex_isPathConnected (pick i)).isConnected,
    A.edgeComponentComplex_pure (pick i) hpure, ?_, ?_,
    (hcomponents i).2.2.2.2.1, hHC, ?_, number, sigma, hcancel⟩
  · intro t ht htc
    rw [A.edgeComponentComplex_cofaces (pick i) ht 3]
    exact hcofaces t (hJA ht) htc
  · intro p hp
    rw [A.edgeComponentComplex_vertex_link (pick i) hp]
    exact hlinks p (hJA hp)
  · intro z hz
    change phi (g z) = z
    rw [hg ⟨z, hJS hz⟩, ← hH (H.symm ⟨z, hJS hz⟩), H.apply_symm_apply]

end PoincareConjecture.M76
