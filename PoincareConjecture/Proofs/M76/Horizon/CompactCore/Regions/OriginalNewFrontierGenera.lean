import PoincareConjecture.Proofs.M76.Wall.OriginalNewFrontierModels
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.OriginalComponentGenus
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Loops.EssentialRimComponent

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem PLDomain.exists_new_frontier_component_genera
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N B F R C : Set X}
    (he : PLDomain e N) (hN : IsCompact N) (hNne : N.Nonempty)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier N = B ∪ F) (hFne : F.Nonempty)
    (hFU : F ⊆ R \ C)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x), ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
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
      (⋃ i, S i) = F ∧ (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
        (∀ x ∈ S i, connectedComponentIn F x = S i) ∧
        ∃ HC : (A.edgeComponentComplex (pick i)).space ≃ₜ S i,
          ∀ z, (HC z : X) = (g z : X)) ∧
      (∀ i, Nat.card (A.edgeComponentComplex (pick i)).vertices +
        Nat.card (Triangle
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
        2 * genus i = Nat.card (Edge
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) ∧
      (∀ i, genus i = 0 → Nonempty (ChartwisePLSphere e (S i))) ∧
      ∀ gamma : C(Metric.sphere (0 : Fin 2 → ℝ) 1, F),
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 →
        ∃ (i : Fin n) (gammaS : C(Metric.sphere (0 : Fin 2 → ℝ) 1, S i)),
          (∀ u, (gamma u : X) ∈ S i) ∧
          (∀ u, (gammaS u : X) = (gamma u : X)) ∧
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gammaS.continuous)) ≠ 1 ∧
          0 < genus i := by
  classical
  obtain ⟨s, phi, K, A, H, g, HB, n, pick, S, hphi, hphiPL, hK, hAK, hA, _, _, _, hH,
    _, hg, hgPL, _, _, hboundary, hstars, hpure, hcofaces, hlinks, hn, hS,
    hunion, hdisjoint, hcomponents, hsphere⟩ :=
    he.exists_new_frontier_component_models hN hNne hB hF hBF hfront hFne
  have hgi : InjOn (fun z => (g z : X)) K.space := by
    intro x hx y hy hxy
    have hinv : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hinv)
  have hphiInj : InjOn phi N := by
    intro x hx y hy hxy
    have hh : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  have hphi_g (z) (hz : z ∈ K.space) : phi (g z) = z := by
    rw [hg ⟨z, hz⟩, ← hH, H.apply_symm_apply]
  have hboundaryMap : MapsTo (fun z => (g z : X)) A.space (frontier N) := by
    intro z hz
    exact (hboundary z (SimplicialComplex.space_subset_of_le hAK hz)).mpr hz
  have hgenus (i : Fin n) : ∃ genus : ℕ,
      Nat.card (A.edgeComponentComplex (pick i)).vertices +
        Nat.card (Triangle
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
        2 * genus = Nat.card (Edge
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
    obtain ⟨_, _, hSF, _, _, HC, hHC⟩ := hcomponents i
    obtain ⟨genus, number, sigma, hcount, _⟩ :=
      exists_original_frontier_component_genus_count e he.cover he.compatible
        K A hAK hA hpure hcofaces hlinks (fun z => (g z : X)) N hgi
        hboundaryMap hstars (pick i) HC hHC hSF hFU hloops
    exact ⟨genus, hcount⟩
  choose genus hcount using hgenus
  refine ⟨s, phi, K, A, g, n, pick, S, genus, hphi, hphiInj, hphiPL, hphi_g,
    hK, hAK, hA, hgPL, hgi,
    hpure, hcofaces, hlinks, hn, hS, hunion, hdisjoint, ?_, hcount, ?_, ?_⟩
  · intro i
    obtain ⟨hc, hconn, hSF, hcomponent, _, HC, hHC⟩ := hcomponents i
    exact ⟨hc, hconn, hSF, hcomponent, HC, hHC⟩
  · intro i hi
    apply hsphere i
    simpa only [hi, Nat.mul_zero, Nat.add_zero] using hcount i
  · intro gamma hessential
    obtain ⟨i, gammaS, hvalues, heq, hessentialS, _⟩ :=
      exists_whole_component_essential_rim e S hunion
        (fun i => (hcomponents i).2.2.2.1) gamma hessential
    exact ⟨i, gammaS, hvalues, heq, hessentialS,
      original_component_genus_pos_of_essential_rim K A hK hAK hgPL hgi
        hpure hcofaces hlinks (pick i) (hS i) gammaS hessentialS (genus i) (hcount i)⟩

end PoincareConjecture.M76
