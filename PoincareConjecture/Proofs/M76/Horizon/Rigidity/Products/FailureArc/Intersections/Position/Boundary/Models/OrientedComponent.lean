import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.Component
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.FrontierSigns

set_option autoImplicit false
open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_oriented_component_model
    {X ι : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hS : S ⊆ frontier R) (x : S)
    (hcomponent : connectedComponentIn (frontier R) (x : X) = S)
    (O : LocalOrientation X) :
    ∃ (s : Finset R) (phi : X → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X)
      (H : J.space ≃ₜ S)
      (number : J.vertices ↪ ℕ)
      (sign : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ IsConnected J.space ∧
      (∀ t ∈ J.faces, ∃ u ∈ J.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ J.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ J.vertices, IsConnected (J.faceLink {p}).space) ∧
      PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, g z = (H z : X)) ∧
      (∀ z ∈ J.space, phi (g z) = z) ∧
      (∀ t u : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex, t ≠ u →
        ∀ a : Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          a.val ⊆ t.val → a.val ⊆ u.val →
          (sign t + boundaryFaceParity number t.val a.val) +
            (sign u + boundaryFaceParity number u.val a.val) = 1) := by
  classical
  have hx : (x : X) ∈ frontier R := hS x.property
  obtain ⟨s, phi, K, A, HK, g, HB, n, pick, T,
      hphi, hphiPL, hK, hAK, hA, _, _, _, hHK, _, hg, hgPL, _, _, hboundary,
      hstars, hpure, hcofaces, hlinks, _, _, hunion, _, hcomponents, _⟩ :=
    he.exists_new_frontier_component_models hR
      ⟨x, he.closed.frontier_subset hx⟩ isClosed_empty isClosed_frontier
      (by simp) (empty_union _).symm ⟨x, hx⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hunion.symm ▸ hx)
  have hTi : T i = S := ((hcomponents i).2.2.2.1 x hi).symm.trans hcomponent
  let J := A.edgeComponentComplex (pick i)
  have hJA : J ≤ A := A.edgeComponentComplex_le (pick i)
  have hJK : J ≤ K := hJA.trans hAK
  have hJS : J.space ⊆ K.space := SimplicialComplex.space_subset_of_le hJK
  obtain ⟨HC, hHC⟩ := (hcomponents i).2.2.2.2.2
  have hgi : InjOn (fun z => (g z : X)) K.space := by
    intro u hu v hv huv
    have hh : HK.symm ⟨u, hu⟩ = HK.symm ⟨v, hv⟩ :=
      Subtype.ext ((hg ⟨u, hu⟩).symm.trans (huv.trans (hg ⟨v, hv⟩)))
    exact congrArg Subtype.val (HK.symm.injective hh)
  have hfront : MapsTo (fun z => (g z : X)) J.space (frontier R) := by
    intro z hz
    exact (hboundary z (hJS hz)).mpr (SimplicialComplex.space_subset_of_le hJA hz)
  obtain ⟨number, sign, hsign⟩ :=
    exists_frontier_all_edge_signs_of_localOrientation O e he.cover he.compatible K J hJK
      (hA.subset hJA) (fun z => (g z : X)) R hgi
      (hgPL.continuousOn.mono hJS) hfront hstars
  refine ⟨s, phi, J, fun z => g z, HC.trans (Homeomorph.setCongr hTi), number, sign,
    hphi, hphiPL, hA.subset hJA,
    (A.edgeComponentComplex_isPathConnected (pick i)).isConnected,
    A.edgeComponentComplex_pure (pick i) hpure, ?_, ?_,
    (hcomponents i).2.2.2.2.1, (fun z => (hHC z).symm), ?_, hsign⟩
  · intro t ht htc
    rw [A.edgeComponentComplex_cofaces (pick i) ht 3]
    exact hcofaces t (hJA ht) htc
  · intro p hp
    rw [A.edgeComponentComplex_vertex_link (pick i) hp]
    exact hlinks p (hJA hp)
  · intro z hz
    change phi (g z) = z
    rw [hg ⟨z, hJS hz⟩, ← hHK (HK.symm ⟨z, hJS hz⟩), HK.apply_symm_apply]

end PoincareConjecture.M76
