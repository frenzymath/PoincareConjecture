import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedCompressionLoops
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.OriginalNewFrontierGenera









set_option autoImplicit false

open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

open Classical in
theorem OriginalDiskProduct.exists_compressed_frontier_component_genera
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U N F Fnew R C : Set X}
    {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hF : IsCompact F)
    (hcut : U ∩ frontier L = F) (hUY : U ⊆ R \ C)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(3 / 4 : ℝ)) (3 / 4)))))
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C)
    (hBC : frontier R ⊆ C)
    (he : PLDomain e N) (hN : IsCompact N) (hFnew : IsCompact Fnew)
    (hfront : frontier N = frontier R ∪ Fnew)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (hne : Fnew.Nonempty) :
    Fnew ⊆ R \ C ∧
    (∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' Fnew) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) ∧
    ∃ (s : Finset N) (phi : X → (s → ℝ × V3))
      (K A : SimplicialComplex ℝ (s → ℝ × V3))
      (g : (s → ℝ × V3) → N)
      (n : ℕ) (pick : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (S : Fin n → Set X) (genus : Fin n → ℕ),
      Continuous phi ∧ InjOn phi N ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      (∀ z ∈ K.space, phi (g z) = z) ∧
      K.faces.Finite ∧ A ≤ K ∧ A.faces.Finite ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      InjOn (fun z => (g z : X)) K.space ∧
      (∀ t ∈ A.faces, ∃ u ∈ A.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ A.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ A.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space) ∧
      0 < n ∧
      (∀ i, S i = (fun z => (g z : X)) '' (A.edgeComponentComplex (pick i)).space) ∧
      (⋃ i, S i) = Fnew ∧ (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ Fnew ∧
        (∀ x ∈ S i, connectedComponentIn Fnew x = S i) ∧
        ∃ HC : (A.edgeComponentComplex (pick i)).space ≃ₜ S i,
          ∀ z, (HC z : X) = (g z : X)) ∧
      (∀ i, Nat.card (A.edgeComponentComplex (pick i)).vertices +
        Nat.card (Triangle
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
        2 * genus i = Nat.card (Edge
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) ∧
      (∀ i, genus i = 0 → Nonempty (ChartwisePLSphere e (S i))) ∧
      ∀ gamma : C(Q, Fnew),
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 →
        ∃ (i : Fin n) (gammaS : C(Q, S i)),
          (∀ u, (gamma u : X) ∈ S i) ∧
          (∀ u, (gammaS u : X) = (gamma u : X)) ∧
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gammaS.continuous)) ≠ 1 ∧
          0 < genus i := by
  have hFY : F ⊆ R \ C := (hcut.symm.subset.trans inter_subset_left).trans hUY
  have hPY : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) (R \ C) :=
    fun z hz => hUY (hsmall hz)
  have hnewY : Fnew ⊆ R \ C := hnew.subset.trans
    (P.compressed_frontier_subset_block.trans (P.frontier_block_subset hFY hPY))
  have hnewloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' Fnew) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C := by
    rw [hnew]
    exact P.protected_compression_frontier_loops hF hcut hUY hsmall hlateral hloops
  have hBF : Disjoint (frontier R) Fnew := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (hnewY hy).2 (hBC hx)
  have hNne : N.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have hxfront : x ∈ frontier N := hfront.symm ▸ Or.inr hx
    exact ⟨x, hN.isClosed.closure_eq ▸ frontier_subset_closure hxfront⟩
  exact ⟨hnewY, hnewloops, he.exists_new_frontier_component_genera hN hNne
    isClosed_frontier hFnew.isClosed hBF hfront hne hnewY hnewloops⟩

end PoincareConjecture.M76
