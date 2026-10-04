import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Regions.OriginalFrontierCompressionAlternative
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Regions.ProtectedCollaredPolygonFilling
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Regions.ProtectedOpenRegion

/-!
# Polygonal fillings from the whole protected frontier

Construct the actual frontier components and their essential rims, fill them
using the retained weak-end homotopies, and apply the collared general-position
construction. The initial essential rim and both one-sided rim homotopies are
retained for the subsequent innermost-circle argument. See Wall005, steps 1--4,
and Hatcher, Corollary 3.3, printed p. 48.
-/

set_option autoImplicit false

open Set Metric Geometry unitInterval

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1

theorem PLDomain.exists_new_frontier_spheres_or_protected_polygon_fillings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N F R C : Set X}
    (he : PLDomain e N) (hN : IsCompact N)
    (hF : IsCompact F) (hFne : F.Nonempty) (hFR : F ⊆ R)
    (hBF : Disjoint (frontier R) F) (hfront : frontier N = frontier R ∪ F)
    (hC : IsCompact C) (hBC : frontier R ⊆ C)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' N))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' N) =
      (Subtype.val : R → X) ⁻¹' F)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    ∃ (n : ℕ) (S : Fin n → Set X), 0 < n ∧ (⋃ i, S i) = F ∧
      (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
        ∀ x ∈ S i, connectedComponentIn F x = S i) ∧
      ∀ i, Nonempty (ChartwisePLSphere e (S i)) ∨
        ∃ (g : V2 → X) (T : Set (Set V2)) (gamma : C(Q, F))
          (A B : C(I × Q, (R \ C : Set X))),
          PolyhedralPLInCharts e g D ∧ MapsTo g D (R \ C) ∧
          (∀ x : Q, (gamma x : X) ∈ S i) ∧ Topology.IsEmbedding gamma ∧
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 ∧
          T.Finite ∧
          (∀ s ∈ T, ∃ m : ℕ, ∃ p : Polygon V2 (m + 3),
            Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s) ∧
          T.PairwiseDisjoint id ∧ D ∩ g ⁻¹' F = ⋃ s ∈ T, s ∧
          (∀ s ∈ T, s ⊆ interior D) ∧
          (∀ u : Q, (A (0, u) : X) = (gamma u : X)) ∧
          (∀ u : Q, A (1, u) = B (0, u)) ∧
          (∀ u : Q, (B (1, u) : X) = g u) ∧
          (∀ (t : I) (u : Q), 0 < (t : ℝ) → (A (t, u) : X) ∈ interior N) ∧
          (∀ (t : I) (u : Q), (B (t, u) : X) ∈ interior N) ∧
          ∀ x ∈ Q, g x ∈ interior N := by
  obtain ⟨hY, hFY, hcut⟩ :=
    Set.protected_open_cut_region hC.isClosed hBC hFR hprotect hrel hfront
  have hNne : N.Nonempty := by
    obtain ⟨x, hx⟩ := hFne
    refine ⟨x, he.closed.frontier_subset ?_⟩
    rw [hfront]
    exact Or.inr hx
  obtain ⟨n, S, hn, hcover, hdisjoint, hcomponents, halt⟩ :=
    he.exists_new_frontier_spheres_or_protected_fillings hN hNne isClosed_frontier
      hF.isClosed hBF hfront hFne hFY hloops
  refine ⟨n, S, hn, hcover, hdisjoint, hcomponents, ?_⟩
  intro i
  rcases halt i with hsphere | ⟨b, gamma, f, _, hgammaS, hemb, _, hessential, hf⟩
  · exact Or.inl hsphere
  · obtain ⟨g, T, A, B, hg, hgY, hT, hpoly, hpair, hpreimage, hinside,
      hA0, hAB, hB1, hAside, hBside, hgr⟩ :=
      he.exists_protected_collared_polygon_filling hY hF hFne hcut gamma f hf
    exact Or.inr ⟨g, T, gamma, A, B, hg, hgY, hgammaS, hemb, hessential,
      hT, hpoly, hpair, hpreimage, hinside, hA0, hAB, hB1, hAside, hBside, hgr⟩

end PoincareMT.M76
