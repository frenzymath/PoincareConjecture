import PoincareConjecture.Proofs.M76.Wall.ConnectedWeakEndCore
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.OriginalNewFrontierGenera
import PoincareConjecture.Proofs.M76.Wall.CompressionComplexity
import PoincareConjecture.Proofs.M76.Wall.ProtectedOpenRegion
import Mathlib.Order.WellFounded











set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem exists_minimal_protected_core_genus
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R A : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R) (hB : IsCompact (frontier R))
    (hend : HasOneSimplyConnectedEnd R) (hA : IsCompact A) (hAR : A ⊆ R) :
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ PLDomain e C ∧ C ⊆ R ∧
      frontier R ⊆ C ∧
      (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
        interior ((Subtype.val : R → X) ⁻¹' C) ∧
      let admissible : ℕ → Prop := fun complexity =>
        ∃ K F : Set X, IsCompact K ∧ IsConnected K ∧ PLDomain e K ∧
          C ⊆ K ∧ K ⊆ R ∧ F.Nonempty ∧ IsCompact F ∧ F ⊆ interior R ∧
          Disjoint (frontier R) F ∧ frontier K = frontier R ∪ F ∧
          frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' F ∧
          (Subtype.val : R → X) ⁻¹' C ⊆
            interior ((Subtype.val : R → X) ⁻¹' K) ∧
          (∀ (x : R) (p : Path x x),
            (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
            ∃ H : p.Homotopy (Path.refl x),
              ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) ∧
          ∃ (Z : Set X) (s : Finset Z) (B : SimplicialComplex ℝ (s → ℝ × V3))
            (g : (s → ℝ × V3) → X) (n : ℕ)
            (pick : Fin n ↪ B.vertexAbstractComplex.edgeGraph.ConnectedComponent)
            (S : Fin n → Set X) (genus : Fin n → ℕ),
            B.faces.Finite ∧ (∀ t ∈ B.faces, t.card ≤ 3) ∧
            PolyhedralPLInCharts e g B.space ∧ InjOn g B.space ∧
            (∀ i, S i = g '' (B.edgeComponentComplex (pick i)).space) ∧
            (⋃ i, S i) = F ∧ (Pairwise fun i j => Disjoint (S i) (S j)) ∧
            (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
              ∀ x ∈ S i, connectedComponentIn F x = S i) ∧
            (∀ i, Nat.card (B.edgeComponentComplex (pick i)).vertices +
              Nat.card (Triangle
                (B.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
              2 * genus i = Nat.card (Edge
                (B.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) ∧
            Wall.compressionComplexity ((List.finRange n).map genus) = complexity;
      ∃ complexity, admissible complexity ∧
        ∀ smaller, admissible smaller → ¬smaller < complexity := by
  classical
  obtain ⟨C, hC, hCconn, hCPL, hCR, hCprotect, D, _, _, _,
    K, F, hK, hKconn, hCK, hKR, hKPL, hFne, hF, hFi, hBF, hfront,
    hprotect, _, hrel, _, hloops⟩ :=
    exists_connected_weak_end_protected_PL_core e hR hRconn hB hend hA hAR
  have hBC : frontier R ⊆ C := by
    intro x hx
    have hxR := hR.closed.frontier_subset hx
    have hxC : (⟨x, hxR⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' C :=
      interior_subset (hCprotect (show (⟨x, hxR⟩ : R) ∈
        (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) from Or.inr hx))
    exact hxC
  obtain ⟨_, hFY, _⟩ := Set.protected_open_cut_region hC.isClosed hBC
    (hFi.trans interior_subset) hprotect hrel hfront
  obtain ⟨s, phi, Kmodel, B, g, n, pick, S, genus,
    _, _, _, _, _, hBK, hBfinite, hg, hgi,
    hpure, _, _, _, hS, hcover, hdisjoint, hcomponents, hcount, _, _⟩ :=
    hKPL.exists_new_frontier_component_genera hK hKconn.nonempty isClosed_frontier
      hF.isClosed hBF hfront hFne hFY hloops
  have hBS : B.space ⊆ Kmodel.space := SimplicialComplex.space_subset_of_le hBK
  have hdim : ∀ t ∈ B.faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, htu, hu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq hu
  refine ⟨C, hC, hCconn, hCPL, hCR, hBC, hCprotect, ?_⟩
  dsimp only
  apply Nat.lt_wfRel.wf.has_min
  refine ⟨Wall.compressionComplexity ((List.finRange n).map genus),
    K, F, hK, hKconn, hKPL, hCK, hKR, hFne, hF, hFi, hBF, hfront, hrel,
    hprotect, hloops, K, s, B, (fun z => (g z : X)), n, pick, S, genus,
    hBfinite, hdim, hg.restrict_finite B hBfinite hBS, hgi.mono hBS,
    hS, hcover, hdisjoint, ?_, hcount, rfl⟩
  intro i
  exact ⟨(hcomponents i).1, (hcomponents i).2.1,
    (hcomponents i).2.2.1, (hcomponents i).2.2.2.1⟩

end PoincareConjecture.M76
