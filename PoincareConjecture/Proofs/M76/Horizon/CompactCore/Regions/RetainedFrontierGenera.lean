import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.RetainedFrontierComponents
import PoincareConjecture.Proofs.M76.Wall.OriginalNewFrontierModels

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical in
theorem exists_retained_frontier_component_genera
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K A : SimplicialComplex ℝ E) (g : E → X)
    {L F : Set X} (x : X) (hFL : F ⊆ L)
    {n : ℕ} (pickOld : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (S : Fin n → Set X) (genus : Fin n → ℕ)
    (hK : K.faces.Finite) (hAK : A ≤ K) (hA : A.faces.Finite)
    (hgPL : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hpure : ∀ t ∈ A.faces, ∃ u ∈ A.faces, t ⊆ u ∧ u.card = 3)
    (hcofaces : ∀ t ∈ A.faces, t.card = 2 →
      {u : Finset E | u ∈ A.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    (hS : ∀ i, S i = g '' (A.edgeComponentComplex (pickOld i)).space)
    (hcover : (⋃ i, S i) = F)
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hcomponents : ∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
      (∀ y ∈ S i, connectedComponentIn F y = S i) ∧
      ∃ HC : (A.edgeComponentComplex (pickOld i)).space ≃ₜ S i,
        ∀ z, (HC z : X) = g z)
    (hcount : ∀ i, Nat.card (A.edgeComponentComplex (pickOld i)).vertices +
      Nat.card (Triangle
        (A.edgeComponentComplex (pickOld i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * genus i = Nat.card (Edge
        (A.edgeComponentComplex (pickOld i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2)
    (hsphere : ∀ i, genus i = 0 → Nonempty (ChartwisePLSphere e (S i)))
    (hne : (F ∩ connectedComponentIn L x).Nonempty) :
    ∃ (kept : List (Fin n)) (pick : Fin kept.length ↪ Fin n)
      (pickNew : Fin kept.length ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent),
      kept.Sublist (List.finRange n) ∧ kept.Nodup ∧ 0 < kept.length ∧
      (∀ i, pick i = kept.get i) ∧
      (∀ i, i ∈ kept ↔ S i ⊆ connectedComponentIn L x) ∧
      (∀ i, pickNew i = pickOld (pick i)) ∧
      K.faces.Finite ∧ A ≤ K ∧ A.faces.Finite ∧
      PolyhedralPLInCharts e g K.space ∧ InjOn g K.space ∧
      (∀ t ∈ A.faces, ∃ u ∈ A.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ A.faces, t.card = 2 →
        {u : Finset E | u ∈ A.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space) ∧
      (∀ i, S (pick i) = g '' (A.edgeComponentComplex (pickNew i)).space) ∧
      (⋃ i, S (pick i)) = F ∩ connectedComponentIn L x ∧
      (Pairwise fun i j => Disjoint (S (pick i)) (S (pick j))) ∧
      (∀ i, IsCompact (S (pick i)) ∧ IsConnected (S (pick i)) ∧
        S (pick i) ⊆ F ∩ connectedComponentIn L x ∧
        (∀ y ∈ S (pick i),
          connectedComponentIn (F ∩ connectedComponentIn L x) y = S (pick i)) ∧
        ∃ HC : (A.edgeComponentComplex (pickNew i)).space ≃ₜ S (pick i),
          ∀ z, (HC z : X) = g z) ∧
      (∀ i, Nat.card (A.edgeComponentComplex (pickNew i)).vertices +
        Nat.card (Triangle
          (A.edgeComponentComplex (pickNew i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
        2 * genus (pick i) = Nat.card (Edge
          (A.edgeComponentComplex (pickNew i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) ∧
      (∀ i, genus (pick i) = 0 → Nonempty (ChartwisePLSphere e (S (pick i)))) ∧
      (List.finRange kept.length).map (genus ∘ pick) = kept.map genus ∧
      ((List.finRange kept.length).map (genus ∘ pick)).Sublist
        ((List.finRange n).map genus) ∧
      Wall.compressionComplexity ((List.finRange kept.length).map (genus ∘ pick)) ≤
        Wall.compressionComplexity ((List.finRange n).map genus) := by
  obtain ⟨kept, pick, hsub, hnd, hpos, hpick, hmem, hunion, hdisj, hcomp, hgenera⟩ :=
    Set.exists_retained_frontier_component_labels_with_reindexed_genera S x hFL
      (fun i => (hcomponents i).2.1) hdisjoint hcover
      (fun i => (hcomponents i).2.2.2.1) hne
  let pickNew := pick.trans pickOld
  obtain ⟨_, _, heq, hsubg, hle⟩ := hgenera genus
  refine ⟨kept, pick, pickNew, hsub, hnd, hpos, hpick, hmem, fun _ => rfl,
    hK, hAK, hA, hgPL, hgi, hpure, hcofaces, hlinks, fun i => hS (pick i),
    hunion, hdisj, ?_, fun i => hcount (pick i), fun i => hsphere (pick i), heq, hsubg, hle⟩
  intro i
  obtain ⟨hc, hconn, _, _, HC, hHC⟩ := hcomponents (pick i)
  refine ⟨hc, hconn, ?_, hcomp i, HC, hHC⟩
  intro y hy
  exact hunion.subset (mem_iUnion.mpr ⟨i, hy⟩)

end PoincareConjecture.M76
