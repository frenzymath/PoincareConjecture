import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressedFrontierGenera
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionGenusDecrease
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.RetainedFrontierGenera










set_option autoImplicit false

open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

open Classical in
set_option maxHeartbeats 800000 in
theorem exists_retained_compression_genera
    {Eold X ι : Type*}
    [NormedAddCommGroup Eold] [NormedSpace ℝ Eold] [FiniteDimensional ℝ Eold]
    [DecidableEq Eold]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    {L U N W F Fnew R C : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F) (hUY : U ⊆ R \ C)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      IsOpen ((Subtype.val : frontier L → X) ⁻¹'
        (P.map '' (Q ×ˢ Ioo (-ε) ε))))
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C)
    (hBC : frontier R ⊆ C)
    (hN : PLDomain e N) (hNc : IsCompact N) (hFnew : IsCompact Fnew)
    (hfront : frontier N = frontier R ∪ Fnew)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (x : X) (hne : (Fnew ∩ connectedComponentIn N x).Nonempty)
    (hW : PLDomain e W) (hWc : IsCompact W) (hcontain : F ∪ P.closedStrip ⊆ W)
    (rim : C(Q, F)) (hrim : ∀ u : Q, (rim u : X) = j u)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (Aold : SimplicialComplex ℝ Eold) (hAold : Aold.faces.Finite)
    (hdimOld : ∀ s ∈ Aold.faces, s.card ≤ 3)
    {oldN : ℕ}
    (pickOld : Fin oldN ↪ Aold.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (gold : Eold → X)
    (hgold : PolyhedralPLInCharts e gold Aold.space) (hgoldi : InjOn gold Aold.space)
    (Old : Fin oldN → Set X)
    (hOldImage : ∀ i, Old i = gold '' (Aold.edgeComponentComplex (pickOld i)).space)
    (hOldCompact : ∀ i, IsCompact (Old i)) (hOldConn : ∀ i, IsConnected (Old i))
    (hOldCover : (⋃ i, Old i) = F)
    (hOldComponents : ∀ i, ∀ y ∈ Old i, connectedComponentIn F y = Old i)
    (hOldDisjoint : Pairwise fun i k => Disjoint (Old i) (Old k))
    (oldGenus : Fin oldN → ℕ)
    (hOldGenus : ∀ i, Nat.card (Aold.edgeComponentComplex (pickOld i)).vertices +
      Nat.card (Triangle
        (Aold.edgeComponentComplex (pickOld i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * oldGenus i = Nat.card (Edge
        (Aold.edgeComponentComplex (pickOld i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    Fnew ⊆ R \ C ∧
    (∀ (y : R) (p : Path y y),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' Fnew) →
      ∃ H : p.Homotopy (Path.refl y),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) ∧
    ∃ (s : Finset N) (phi : X → (s → ℝ × V3))
      (K A : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → N)
      (n : ℕ) (pickRaw : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (S : Fin n → Set X) (genus : Fin n → ℕ)
      (kept : List (Fin n)) (select : Fin kept.length ↪ Fin n)
      (pick : Fin kept.length ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent),
      Continuous phi ∧ InjOn phi N ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      (∀ z ∈ K.space, phi (g z) = z) ∧
      kept.Sublist (List.finRange n) ∧ kept.Nodup ∧ 0 < kept.length ∧
      (∀ i, select i = kept.get i) ∧
      (∀ i, i ∈ kept ↔ S i ⊆ connectedComponentIn N x) ∧
      (∀ i, pick i = pickRaw (select i)) ∧
      K.faces.Finite ∧ A ≤ K ∧ A.faces.Finite ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      InjOn (fun z => (g z : X)) K.space ∧
      (∀ t ∈ A.faces, ∃ u ∈ A.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ A.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ A.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space) ∧
      (∀ i, S i = (fun z => (g z : X)) '' (A.edgeComponentComplex (pickRaw i)).space) ∧
      (⋃ i, S i) = Fnew ∧
      (∀ i, S (select i) = (fun z => (g z : X)) '' (A.edgeComponentComplex (pick i)).space) ∧
      (⋃ i, S (select i)) = Fnew ∩ connectedComponentIn N x ∧
      (Pairwise fun i k => Disjoint (S (select i)) (S (select k))) ∧
      (∀ i, IsCompact (S (select i)) ∧ IsConnected (S (select i)) ∧
        S (select i) ⊆ Fnew ∩ connectedComponentIn N x ∧
        (∀ y ∈ S (select i),
          connectedComponentIn (Fnew ∩ connectedComponentIn N x) y = S (select i)) ∧
        ∃ HC : (A.edgeComponentComplex (pick i)).space ≃ₜ S (select i),
          ∀ z, (HC z : X) = (g z : X)) ∧
      (∀ i, Nat.card (A.edgeComponentComplex (pick i)).vertices +
        Nat.card (Triangle
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
        2 * genus (select i) = Nat.card (Edge
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) ∧
      (∀ i, genus (select i) = 0 → Nonempty (ChartwisePLSphere e (S (select i)))) ∧
      (List.finRange kept.length).map (genus ∘ select) = kept.map genus ∧
      ((List.finRange kept.length).map (genus ∘ select)).Sublist
        ((List.finRange n).map genus) ∧
      Wall.compressionComplexity ((List.finRange n).map genus) <
        Wall.compressionComplexity ((List.finRange oldN).map oldGenus) ∧
      Wall.compressionComplexity ((List.finRange kept.length).map (genus ∘ select)) <
        Wall.compressionComplexity ((List.finRange oldN).map oldGenus) := by
  have hF : IsCompact F := hOldCover ▸ isCompact_iUnion hOldCompact
  obtain ⟨hnewY, hnewloops, s, phi, K, A, g, n, pickRaw, S, genus,
    hphi, hphii, hphiPL, hinverse, hK, hAK, hA, hg, hgi,
    hpure, hcofaces, hlinks, _, hS, hcover, hdisjoint, hcomponents, hcount, hsphere, _⟩ :=
    P.exists_compressed_frontier_component_genera hF hcut hUY hsmall
      (hlateral (3 / 4) (by norm_num) (by norm_num)) hloops hBC
      hN hNc hFnew hfront hnew (hne.mono inter_subset_left)
  refine ⟨hnewY, hnewloops, s, phi, K, A, g, n, pickRaw, S, genus, ?_⟩
  have hFN : Fnew ⊆ N := by
    intro y hy
    exact hNc.isClosed.closure_eq ▸ frontier_subset_closure (hfront.symm ▸ Or.inr hy)
  have hAS : A.space ⊆ K.space := SimplicialComplex.space_subset_of_le hAK
  have hdim : ∀ t ∈ A.faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, htu, hu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq hu
  have hdecrease : Wall.compressionComplexity ((List.finRange n).map genus) <
      Wall.compressionComplexity ((List.finRange oldN).map oldGenus) :=
    P.compressionComplexity_decreases (Eold := Eold) (Enew := s → ℝ × V3)
    (N := W) (n := oldN) (m := n) hcut hsmall
    (hlateral (1 / 2) (by norm_num) (by norm_num)) hnew hW hWc hcontain
    rim hrim hessential Aold A hAold hA hdimOld hdim pickOld pickRaw gold
    (fun z => (g z : X)) hgold hgoldi (hg.restrict_finite A hA hAS) (hgi.mono hAS)
    Old S hOldImage hS hOldCompact hOldConn hOldCover hOldComponents hOldDisjoint
    (fun i => (hcomponents i).1) (fun i => (hcomponents i).2.1) hcover
    (fun i => (hcomponents i).2.2.2.1) hdisjoint
    phi hphiPL (hphii.mono hFN) (fun z hz => hinverse z (hAS hz))
    oldGenus genus hOldGenus hcount hsphere
  obtain ⟨kept, select, pick, hsub, hnd, hpos, hselect, hmem, hpick,
    _, _, _, _, _, _, _, _, himage, hunion, hdisj, hcomp, hgenus, hsph,
    hlist, hsublist, hle⟩ :=
    exists_retained_frontier_component_genera K A (fun z => (g z : X)) x hFN
      pickRaw S genus hK hAK hA hg hgi hpure hcofaces hlinks
      hS hcover hdisjoint hcomponents hcount hsphere hne
  exact ⟨kept, select, pick,
    hphi, hphii, hphiPL, hinverse, hsub, hnd, hpos, hselect, hmem, hpick,
    hK, hAK, hA, hg, hgi, hpure, hcofaces, hlinks, hS, hcover,
    himage, hunion, hdisj, hcomp, hgenus, hsph, hlist, hsublist,
    hdecrease, lt_of_le_of_lt hle hdecrease⟩

end PoincareConjecture.M76.OriginalDiskProduct
