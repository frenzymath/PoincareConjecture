import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalPrimalCutDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualEdges
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleAdjacency

set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]

theorem exists_original_cut_disk_of_euler_zero
    (hconn : IsConnected K.space)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (hzero : K.surfaceEulerCount = 0) :
    ∃ (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
      (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
      (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P),
      P.IsTree ∧ D.IsTree ∧
      let _ : Fintype (ResidualComplementaryEdge K P D) := Fintype.ofFinite _
      ∃ labels : ResidualComplementaryEdge K P D ≃ Fin 2,
        Nonempty (OriginalPrimalCutDiskData K P D hD hcofaces hP labels) := by
  have hK : K.faces.Finite := Set.toFinite _
  have hgraph := K.connected_edgeGraph_of_isConnected hK hconn
  have htri := K.vertex_triangleGraph_connected
    (K.triangleGraph_connected_of_isConnected hK hpure hconn hlinks)
  obtain ⟨P, hP, hPtree, D, hD, hDtree, L, hL, _, hcount⟩ :=
    K.vertexAbstractComplex.exists_primal_dual_trees_with_residual_edges hgraph
      (originalTriangleCofaceCounts K hcofaces) htri
  have hLcard : L.card = 2 := by
    have hvertices := K.surfaceEulerCount_eq_vertex_counts
    rw [hzero] at hvertices
    have hcountInt := congrArg (fun n : ℕ ↦ (n : ℤ)) hcount
    simp only [Nat.cast_add, Nat.cast_ofNat] at hcountInt
    omega
  refine ⟨P, hP, D, hD, hPtree, hDtree, ?_⟩
  let _ : Fintype (ResidualComplementaryEdge K P D) := Fintype.ofFinite _
  let f : ResidualComplementaryEdge K P D → L := fun s ↦
    ⟨complementaryOriginalEdge K P hcofaces s.val,
      (hL _).mpr ⟨s.val, rfl, s.property⟩⟩
  have hfi : Function.Injective f := by
    intro s t heq
    have hv : complementaryOriginalEdge K P hcofaces s.val =
        complementaryOriginalEdge K P hcofaces t.val := congrArg (fun z : L ↦ z.val) heq
    exact residualOriginalEdge_injective K P D hcofaces hv
  have hfs : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨s, hse, hs⟩ := (hL e).mp he
    exact ⟨⟨s, hs⟩, Subtype.ext hse⟩
  let labels : ResidualComplementaryEdge K P D ≃ Fin 2 :=
    (Equiv.ofBijective f ⟨hfi, hfs⟩).trans
      (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hLcard))
  exact ⟨labels, nonempty_originalPrimalCutDiskData K P D hD hcofaces hP labels
    hpure hlinks hPtree hDtree⟩

end PoincareConjecture.M76.OriginalTriangleCopies
