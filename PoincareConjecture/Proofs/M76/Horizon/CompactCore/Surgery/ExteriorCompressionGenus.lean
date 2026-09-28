import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ConnectedExteriorCompression
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ExteriorCompressionLocalFrontier
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.RetainedCompressionGenera









set_option autoImplicit false

open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

open Classical in
set_option maxHeartbeats 800000 in
theorem PLDomain.exists_exterior_compression_genus_decrease
    {Eold X ι : Type*}
    [NormedAddCommGroup Eold] [NormedSpace ℝ Eold] [FiniteDimensional ℝ Eold]
    [DecidableEq Eold]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K C F : Set X} {j : V2 → X}
    (he : PLDomain e K) (hK : IsCompact K) (hR : IsClosed R) (hKR : K ⊆ R)
    (hRconn : IsConnected R) (hend : HasOneSimplyConnectedEnd R)
    (hC : IsClosed C) (hCconn : IsConnected C) (hCR : C ⊆ R)
    (hBC : frontier R ⊆ C) (hF : IsCompact F) (hFR : F ⊆ R)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' K))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' F)
    (hfront : frontier K = frontier R ∪ F)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x), ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hjext : MapsTo j D (interior K)ᶜ) (hjR : MapsTo j D R)
    (hjC : Disjoint (j '' D) C)
    (hproper : ∀ z : D, j z ∈ F ↔ (z : V2) ∈ Q)
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
    (hOldComponents : ∀ i, ∀ y ∈ Old i, _root_.connectedComponentIn F y = Old i)
    (hOldDisjoint : Pairwise fun i k => Disjoint (Old i) (Old k))
    (oldGenus : Fin oldN → ℕ)
    (hOldGenus : ∀ i, Nat.card (Aold.edgeComponentComplex (pickOld i)).vertices +
      Nat.card (Triangle
        (Aold.edgeComponentComplex (pickOld i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * oldGenus i = Nat.card (Edge
        (Aold.edgeComponentComplex (pickOld i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    ∃ M Fout : Set X,
      IsCompact M ∧ IsConnected M ∧ PLDomain e M ∧ C ⊆ M ∧ M ⊆ R ∧
      Fout.Nonempty ∧ IsCompact Fout ∧ Fout ⊆ interior R ∧
      Disjoint (frontier R) Fout ∧ frontier M = frontier R ∪ Fout ∧
      frontier ((Subtype.val : R → X) ⁻¹' M) = (Subtype.val : R → X) ⁻¹' Fout ∧
      ((Subtype.val : R → X) ⁻¹' C ⊆ interior ((Subtype.val : R → X) ⁻¹' M)) ∧
      (∀ (y : R) (p : Path y y),
        (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' Fout) →
        ∃ H : p.Homotopy (Path.refl y), ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) ∧
      ∃ (Z : Set X) (s : Finset Z) (A : SimplicialComplex ℝ (s → ℝ × V3))
        (g : (s → ℝ × V3) → X)
        (n : ℕ) (pick : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
        (S : Fin n → Set X) (genus : Fin n → ℕ),
        A.faces.Finite ∧ (∀ t ∈ A.faces, t.card ≤ 3) ∧
        PolyhedralPLInCharts e g A.space ∧ InjOn g A.space ∧
        (∀ i, S i = g '' (A.edgeComponentComplex (pick i)).space) ∧
        (∀ i, IsCompact (S i)) ∧ (∀ i, IsConnected (S i)) ∧
        (⋃ i, S i) = Fout ∧
        (∀ i, ∀ y ∈ S i, _root_.connectedComponentIn Fout y = S i) ∧
        (Pairwise fun i k => Disjoint (S i) (S k)) ∧
        (∀ i, Nat.card (A.edgeComponentComplex (pick i)).vertices +
          Nat.card (Triangle
            (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
          2 * genus i = Nat.card (Edge
            (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) ∧
        (∀ i, genus i = 0 → Nonempty (ChartwisePLSphere e (S i))) ∧
        Wall.compressionComplexity ((List.finRange n).map genus) <
          Wall.compressionComplexity ((List.finRange oldN).map oldGenus) := by
  classical
  obtain ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, P, Fnew, x, M,
    hsmall, hnewPL, hnewcompact, hnewR, hfoot, heq, hFnew, hnewfront,
    hx, hM, hMc, hMconn, hMPL, hCM, hMsub, hMR, hne, hMFc, hMFi, hdisj,
    hMfront, hMrel, hMprotect, hMBprotect, hMloops, hcollars⟩ :=
    he.exists_connected_protected_exterior_compression hK hR hKR hRconn hend
      hC hCconn hCR hBC hF hFR hprotect hrel hfront hloops
      hj hemb hjext hjR hjC hproper
  obtain ⟨_, _, hcut⟩ :=
    Set.protected_open_cut_region hC hBC hFR hprotect hrel hfront
  have hlocal := he.exterior_compression_local_frontier hPH
    (fun _ hz => hcore (Or.inl hz)) hLE hcut
  have hFK : F ⊆ K := fun _ hz => he.closed.frontier_subset (hfront.symm ▸ Or.inr hz)
  have hcontain : F ∪ P.closedStrip ⊆ K ∪ P.closedStrip :=
    union_subset_union_left _ hFK
  have hne' : (Fnew ∩ _root_.connectedComponentIn (K ∪ P.closedStrip) x).Nonempty := hM ▸ hne
  obtain ⟨_, _, s, phi, B, A, g, n, pickRaw, S, genus, kept, select, pick,
    _, _, _, _, _, _, _, _, _, _, hB, hAB, hA, hg, hgi, hpure, _, _, _, _,
    himage, hunion, hdisjoint, hcomponents, hcount, hsphere, _, _, _, hdecrease⟩ :=
    P.exists_retained_compression_genera hlocal inter_subset_right hsmall
      (fun ε hpos hle => (hcollars ε hpos hle).2.1) hloops hBC
      hnewPL hnewcompact hFnew hnewfront heq x hne'
      hnewPL hnewcompact hcontain rim hrim hessential Aold hAold hdimOld
      pickOld gold hgold hgoldi Old hOldImage hOldCompact hOldConn
      hOldCover hOldComponents hOldDisjoint oldGenus hOldGenus
  have hAS : A.space ⊆ B.space := SimplicialComplex.space_subset_of_le hAB
  have hdim : ∀ t ∈ A.faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, htu, hu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq hu
  refine ⟨M, Fnew ∩ M, hMc, hMconn, hMPL, hCM, hMR, hne, hMFc, hMFi,
    hdisj, hMfront, hMrel, hMprotect, hMloops, K ∪ P.closedStrip, s, A,
    (fun z => (g z : X)), kept.length, pick, S ∘ select, genus ∘ select,
    hA, hdim, hg.restrict_finite A hA hAS, hgi.mono hAS, himage,
    (fun i => (hcomponents i).1), (fun i => (hcomponents i).2.1), ?_, ?_,
    hdisjoint, hcount, hsphere, hdecrease⟩
  · exact hM.symm ▸ hunion
  · intro i y hy
    exact hM.symm ▸ (hcomponents i).2.2.2.1 y hy

end PoincareConjecture.M76
