import PoincareConjecture.Proofs.M76.Wall.OriginalNewFrontierModels

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_component_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hS : S ⊆ frontier R) (x : S)
    (hcomponent : connectedComponentIn (frontier R) (x : X) = S) :
    ∃ (s : Finset R) (phi : X → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X)
      (H : J.space ≃ₜ S),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ IsConnected J.space ∧
      (∀ t ∈ J.faces, ∃ u ∈ J.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ J.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ J.vertices, IsConnected (J.faceLink {p}).space) ∧
      PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, g z = (H z : X)) ∧
      ∀ z ∈ J.space, phi (g z) = z := by
  classical
  have hx : (x : X) ∈ frontier R := hS x.property
  obtain ⟨s, phi, K, A, HK, g, HB, n, pick, T,
      hphi, hphiPL, hK, hAK, hA, _, _, _, hHK, _, hg, _, _, _, _,
      _, hpure, hcofaces, hlinks, _, _, hwhole, _, hcomponents, _⟩ :=
    he.exists_new_frontier_component_models hR
      ⟨x, he.closed.frontier_subset hx⟩ isClosed_empty isClosed_frontier
      (by simp) (empty_union _).symm ⟨x, hx⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hwhole.symm ▸ hx)
  have hTi : T i = S := ((hcomponents i).2.2.2.1 x hi).symm.trans hcomponent
  let J := A.edgeComponentComplex (pick i)
  have hJA : J ≤ A := A.edgeComponentComplex_le (pick i)
  have hJK : J ≤ K := hJA.trans hAK
  have hJS : J.space ⊆ K.space := SimplicialComplex.space_subset_of_le hJK
  obtain ⟨HC, hHC⟩ := (hcomponents i).2.2.2.2.2
  refine ⟨s, phi, J, fun z => g z, HC.trans (Homeomorph.setCongr hTi),
    hphi, hphiPL, hA.subset hJA,
    (A.edgeComponentComplex_isPathConnected (pick i)).isConnected,
    A.edgeComponentComplex_pure (pick i) hpure, ?_, ?_,
    (hcomponents i).2.2.2.2.1, (fun z => (hHC z).symm), ?_⟩
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
