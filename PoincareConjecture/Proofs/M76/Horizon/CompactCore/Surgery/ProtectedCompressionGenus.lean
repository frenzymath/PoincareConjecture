import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.InteriorCompressionGenus
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ExteriorCompressionGenus
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.ProtectedDiskCutSide

set_option autoImplicit false

open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

open Classical in
set_option maxHeartbeats 800000 in
theorem PLDomain.exists_protected_compression_genus_decrease
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
    (hjY : MapsTo j D (R \ C))
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
  obtain ⟨_, _, hcut⟩ :=
    Set.protected_open_cut_region hC hBC hFR hprotect hrel hfront
  have hjR : MapsTo j D R := fun z hz => (hjY hz).1
  have hjC : Disjoint (j '' D) C := by
    apply disjoint_left.mpr
    rintro y ⟨z, hz, rfl⟩ hy
    exact (hjY hz).2 hy
  rcases he.protected_disk_lies_on_one_side hcut hj.continuousOn hjY hproper with
    ⟨hjK, _⟩ | ⟨hjext, _⟩
  · exact he.exists_interior_compression_genus_decrease hK hR hKR hRconn hend
      hC hCconn hCR hBC hF hFR hprotect hrel hfront hloops hj hemb hjK hjC hproper
      rim hrim hessential Aold hAold hdimOld pickOld gold hgold hgoldi
      Old hOldImage hOldCompact hOldConn hOldCover hOldComponents hOldDisjoint
      oldGenus hOldGenus
  · exact he.exists_exterior_compression_genus_decrease hK hR hKR hRconn hend
      hC hCconn hCR hBC hF hFR hprotect hrel hfront hloops hj hemb hjext hjR hjC hproper
      rim hrim hessential Aold hAold hdimOld pickOld gold hgold hgoldi
      Old hOldImage hOldCompact hOldConn hOldCover hOldComponents hOldDisjoint
      oldGenus hOldGenus

end PoincareConjecture.M76
