import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Regions.OriginalNewFrontierModels
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Loops.OriginalFrontierEssentialRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Spheres.OriginalSphereSimplyConnected
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.SurfaceEulerValuation

/-!
# Residual-edge counts of the complete source phase

A closed part of the actual compact PL frontier constructs its finite
component triangulations and their tree-cotree residual counts. Zero
residual count constructs a PL sphere; positive count constructs an
embedded essential original-atlas PL rim. The construction applies to
the physical compressed slab without reselecting the two phases.

These are the component counts used in Waldhausen's hierarchy argument,
pp. 59--60. Comparison across compression is a separate obligation.
-/

set_option autoImplicit false

open Set Geometry Metric PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1

/-- The residual equation stored by a complete phase component is its
geometric surface Euler count.  This is the direct interface between the
tree-cotree data and the finite geometric refinement layer. -/
theorem component_surfaceEulerCount_eq_two_sub_residual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : SimplicialComplex ℝ E) {r : ℕ}
    (h : Nat.card J.vertices +
      Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + r =
      Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    J.surfaceEulerCount = 2 - (r : ℤ) := by
  exact J.surfaceEulerCount_eq_two_sub_residual h

open Classical in
/-- Construct numerical complexity data from the complete geometric phase,
including an actual essential rim for every positive residual count. -/
theorem PLDomain.exists_frontier_component_complexities
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N B F : Set X}
    (he : PLDomain e N) (hN : IsCompact N) (hNne : N.Nonempty)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier N = B ∪ F) (hFne : F.Nonempty) :
    ∃ (s : Finset N) (n : ℕ)
      (J : Fin n → SimplicialComplex ℝ (s → ℝ × V3))
      (g : (s → ℝ × V3) → X) (M : Fin n → Set X) (r : Fin n → ℕ),
      0 < n ∧ (⋃ i, M i) = F ∧ (Pairwise fun i j => Disjoint (M i) (M j)) ∧
      ∀ i, (J i).faces.Finite ∧ IsCompact (M i) ∧ IsConnected (M i) ∧ M i ⊆ F ∧
        (∀ x ∈ M i, connectedComponentIn F x = M i) ∧
        PolyhedralPLInCharts e g (J i).space ∧
        (∃ HC : (J i).space ≃ₜ M i, ∀ z, (HC z : X) = g z) ∧
        Nat.card (J i).vertices +
          Nat.card (Triangle (J i).vertexAbstractComplex.toPreAbstractSimplicialComplex) + r i =
          Nat.card (Edge (J i).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 ∧
        (r i = 0 ↔ Nonempty (ChartwisePLSphere e (M i))) ∧
        (0 < r i → ∃ (v : V2 → X) (gamma : C(Q, M i)),
          Topology.IsEmbedding gamma ∧ PolyhedralPLInCharts e v Q ∧
          (∀ z : Q, (gamma z : X) = v z) ∧
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1) := by
  classical
  obtain ⟨s, u, K, A, H, g, HB, n, pick, M,
    _, _, hK, hAK, hA, _, _, _, _, _, hg, hgPL, _, _, _, _, hpure, hcofaces, hlinks,
    hn, hM, hunion, hdisjoint, hcomponents, hsphere⟩ :=
    he.exists_new_frontier_component_models hN hNne hB hF hBF hfront hFne
  let J := fun i => A.edgeComponentComplex (pick i)
  have hr (i : Fin n) : ∃ r : ℕ,
      Nat.card (J i).vertices +
        Nat.card (Triangle (J i).vertexAbstractComplex.toPreAbstractSimplicialComplex) + r =
        Nat.card (Edge (J i).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
    obtain ⟨P, _, _, D, _, _, L, _, _, hcount⟩ :=
      A.exists_edgeComponent_trees_with_residual_edges hA (pick i) hpure hcofaces hlinks
    exact ⟨L.card, hcount⟩
  choose r hr using hr
  refine ⟨s, n, J, fun z => g z, M, r, hn, hunion, hdisjoint, ?_⟩
  intro i
  obtain ⟨hcompact, hconn, hsub, hcomponent, hPL, HC, hHC⟩ := hcomponents i
  refine ⟨hA.subset (A.edgeComponentComplex_le (pick i)), hcompact, hconn,
    hsub, hcomponent, hPL, ⟨HC, hHC⟩, hr i, ?_⟩
  have hpositive (hpos : 0 < r i) : ∃ (v : V2 → X) (gamma : C(Q, M i)),
      Topology.IsEmbedding gamma ∧ PolyhedralPLInCharts e v Q ∧
      (∀ z : Q, (gamma z : X) = v z) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
    have hcount : Nat.card (J i).vertices +
        Nat.card (Triangle (J i).vertexAbstractComplex.toPreAbstractSimplicialComplex) <
        Nat.card (Edge (J i).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
      have h := hr i
      omega
    obtain ⟨m, P, a, v, gamma, _, _, _, _, _, _, _, _, hgamma, _, hemb, hv, hnontrivial⟩ :=
      exists_original_frontier_essential_rim e A hA (pick i) hpure hcofaces hlinks
        (Subset.refl (M i))
        (fun x hx => hconn.isPreconnected.connectedComponentIn hx)
        HC (fun z => (g z : X)) hHC hPL hcount
    exact ⟨fun z => g (v z), gamma, hemb, hv, hgamma, hnontrivial⟩
  refine ⟨⟨?_, ?_⟩, hpositive⟩
  · intro hzero
    apply hsphere i
    have h := hr i
    simpa only [hzero, Nat.add_zero] using h
  · rintro ⟨sph⟩
    by_contra hnonzero
    obtain ⟨v, gamma, _, _, _, hessential⟩ := hpositive (Nat.pos_of_ne_zero hnonzero)
    let : SimplyConnectedSpace (M i) := sph.simplyConnectedSpace
    exact hessential (Subsingleton.elim _ _)

end PoincareMT.M76
