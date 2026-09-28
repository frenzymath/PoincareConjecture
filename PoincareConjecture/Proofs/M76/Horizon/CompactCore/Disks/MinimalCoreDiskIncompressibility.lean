import PoincareConjecture.Proofs.M76.Horizon.CompactCore.General.MinimalProtectedCoreGenus
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedCompressionGenus

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_protected_core_without_essential_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R A : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R) (hB : IsCompact (frontier R))
    (hend : HasOneSimplyConnectedEnd R) (hA : IsCompact A) (hAR : A ⊆ R) :
    ∃ C K F : Set X,
      IsCompact C ∧ IsConnected C ∧ PLDomain e C ∧ C ⊆ R ∧ frontier R ⊆ C ∧
      (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
        interior ((Subtype.val : R → X) ⁻¹' C) ∧
      IsCompact K ∧ IsConnected K ∧ PLDomain e K ∧ C ⊆ K ∧ K ⊆ R ∧
      F.Nonempty ∧ IsCompact F ∧ F ⊆ interior R ∧ Disjoint (frontier R) F ∧
      frontier K = frontier R ∪ F ∧
      frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' F ∧
      (Subtype.val : R → X) ⁻¹' C ⊆
        interior ((Subtype.val : R → X) ⁻¹' K) ∧
      (∀ (x : R) (p : Path x x),
        (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
        ∃ H : p.Homotopy (Path.refl x),
          ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) ∧
      ∀ j : V2 → X, PolyhedralPLInCharts e j D →
        Topology.IsEmbedding (fun z : D => j z) → MapsTo j D (R \ C) →
        (∀ z : D, j z ∈ F ↔ (z : V2) ∈ Q) →
        ∀ rim : C(Q, F), (∀ u : Q, (rim u : X) = j u) →
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) = 1 := by
  classical
  obtain ⟨C, hC, hCconn, hCPL, hCR, hBC, hCprotect, complexity,
    ⟨K, F, hK, hKconn, hKPL, hCK, hKR, hFne, hF, hFi, hBF, hfront, hrel,
      hprotect, hloops, Z, s, B, g, n, pick, S, genus, hBfinite, hdim, hg, hgi,
      hS, hcover, hdisjoint, hcomponents, hcount, hcomplexity⟩, hmin⟩ :=
    exists_minimal_protected_core_genus e hR hRconn hB hend hA hAR
  refine ⟨C, K, F, hC, hCconn, hCPL, hCR, hBC, hCprotect,
    hK, hKconn, hKPL, hCK, hKR, hFne, hF, hFi, hBF, hfront, hrel,
    hprotect, hloops, ?_⟩
  intro j hj hemb hjY hproper rim hrim
  by_contra hessential
  obtain ⟨M, Fout, hM, hMconn, hMPL, hCM, hMR, hFoutne, hFout, hFouti,
    hBFout, hMfront, hMrel, hMprotect, hMloops,
    Znew, snew, Bnew, gnew, m, pickNew, T, newGenus,
    hBnew, hdimNew, hgnew, hgnewi, hT, hTc, hTconn, hTcover, hTcomp, hTdisj,
    hnewCount, _, hdecrease⟩ :=
    hKPL.exists_protected_compression_genus_decrease hK hR.closed hKR hRconn hend
      hC.isClosed hCconn hCR hBC hF (hFi.trans interior_subset)
      hprotect hrel hfront hloops hj hemb hjY hproper rim hrim hessential
      B hBfinite hdim pick g hg hgi S hS (fun i => (hcomponents i).1)
      (fun i => (hcomponents i).2.1) hcover (fun i => (hcomponents i).2.2.2)
      hdisjoint genus hcount
  apply hmin (Wall.compressionComplexity ((List.finRange m).map newGenus)) ?_ ?_
  · refine ⟨M, Fout, hM, hMconn, hMPL, hCM, hMR, hFoutne, hFout,
      hFouti, hBFout, hMfront, hMrel, hMprotect, hMloops,
      Znew, snew, Bnew, gnew, m, pickNew, T, newGenus,
      hBnew, hdimNew, hgnew, hgnewi, hT, hTcover, hTdisj, ?_, hnewCount, rfl⟩
    intro i
    exact ⟨hTc i, hTconn i,
      (subset_iUnion T i).trans hTcover.subset, hTcomp i⟩
  · exact hdecrease.trans_eq hcomplexity

end PoincareConjecture.M76
