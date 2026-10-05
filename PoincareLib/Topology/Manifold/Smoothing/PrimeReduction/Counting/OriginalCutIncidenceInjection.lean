import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.ConnectedCutGraphBound
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.FiniteComplexHomologyDomain
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.ComponentCycleRankBound
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.ComponentHomologyCount

/-!
# Original sphere systems construct the incidence homology injection

Every cut component, edge, collar coordinate and homotopy is constructed
from the original sphere family. The linear map detects every incidence
cycle by the actual mod-two covers of its cut graph. Cancelling the nonzero
component contributions leaves only zero-homology components in the count.
-/

set_option autoImplicit false

open Set Metric Geometry CategoryTheory
open scoped BigOperators

universe u

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_cut_incidence_injection
    {X κ : Type u} {ι : Type*} [MetricSpace X] [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (Q : Set X) (hfinite : Finite (ConnectedComponents Q))
      (B : κ × Bool → Set X) (H : ∀ b, S b.1 ≃ₜ B b)
      (_sB : ∀ b, ChartwisePLSphere e (B b)) (O : κ → Set X)
      (D : ConnectedComponents Q → Set X) (ends : κ → Bool → ConnectedComponents Q)
      (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i)),
      letI := hfinite
      letI : Fintype (ConnectedComponents Q) := Fintype.ofFinite _
      letI : DecidableEq (ConnectedComponents Q) := Classical.decEq _
      ∃ (q : C(R, CutGraph.carrier ends)) (s : C(CutGraph.carrier ends, R)),
        Q = R \ ⋃ i, O i ∧ IsCompact Q ∧ PLDomain e Q ∧
        (∀ i, IsOpen (O i) ∧ IsCompact (closure (O i)) ∧
          IsConnected (closure (O i)) ∧ closure (O i) ⊆ U ∩ interior R) ∧
        Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) ∧
        (⋃ i, closure (O i)) ∪ Q = R ∧ Q \ U = R \ U ∧
        (∀ c, IsCompact (D c) ∧ PLDomain e (D c) ∧ IsConnected (D c) ∧ D c ⊆ Q ∧
          frontier (D c) = (D c ∩ frontier R) ∪ ⋃ b ∈ {b | ends b.1 b.2 = c}, B b) ∧
        Pairwise (fun c d => Disjoint (D c) (D d)) ∧ (⋃ c, D c) = Q ∧
        (∀ x : Q, D (ConnectedComponents.mk x) = connectedComponentIn Q x) ∧
        (∀ i c, closure (O i) ∩ D c =
          ⋃ b ∈ {b : Bool | ends i b = c}, B (i, b)) ∧
        (∀ i x, (W i (x, 0) : X) = H (i, false) x ∧
          (W i (x, 1) : X) = H (i, true) x) ∧
        (∀ i x, (W i (x, ⟨(1 / 2 : ℝ), by norm_num⟩) : X) = x) ∧
        (∀ v (x : R), (x : X) ∈ D v →
          (q x : CutGraph.Ambient (ConnectedComponents Q) κ) = CutGraph.vertex v) ∧
        (∀ i (x : R) (hi : (x : X) ∈ closure (O i)),
          q x = CutGraph.edgePath ends i (((W i).symm ⟨x, hi⟩).2)) ∧
        (q.comp s).Homotopic (ContinuousMap.id (CutGraph.carrier ends)) ∧
        Function.Injective (CutGraph.sectionIncidenceHomology ends s) ∧
        (IsConnected R → Module.finrank (ZMod 2)
          (LinearMap.ker (CutGraph.incidenceBoundary (K := ZMod 2) ends)) +
            Fintype.card (ConnectedComponents Q) = Fintype.card κ + 1) ∧
        Fintype.card κ ≤ Module.finrank (ZMod 2)
          ↑((TopCat.toSSet.obj (TopCat.of R)).homology
            (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1) +
              Fintype.card (ConnectedComponents Q) ∧
        (IsConnected R → Fintype.card κ + 1 ≤ Module.finrank (ZMod 2)
          ↑((TopCat.toSSet.obj (TopCat.of R)).homology
            (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1) +
              Fintype.card (ConnectedComponents Q)) ∧
        ∃ j : C(Q, R), (∀ x, (j x : X) = x) ∧
          Function.Injective (ModTwoMayerVietoris.homologyMapOf j 1) ∧
          ModTwoMayerVietoris.homologyMapOf j 1 ≫
            ModTwoMayerVietoris.homologyMapOf q 1 = 0 ∧
          (IsConnected R → Fintype.card κ + 1 +
            ∑ v, Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology (D v) 1) ≤
              Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
                Fintype.card (ConnectedComponents Q)) ∧
          (IsConnected R → Fintype.card κ + 1 ≤
            Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
              {v | Limits.IsZero (ModTwoMayerVietoris.homology (D v) 1)}.ncard) := by
  classical
  obtain ⟨Q, hfinite, B, H, sB, O, D, ends, W, q, s, hQeq, hQ, hQPL, hO, hCC,
    hcover, houtside, hD, hDD, hDcover, hactual, hinc, hW, hcenter, hqD, hqC, hqs⟩ :=
    exists_original_sphere_cut_graph_homotopy_retract S sS hdis hR he hSR hU hSU
  let := hfinite
  let : Fintype (ConnectedComponents Q) := Fintype.ofFinite _
  let := he.finite_modTwo_homology hR 1
  have hincQ (i : κ) : closure (O i) ∩ Q = B (i, false) ∪ B (i, true) := by
    ext x
    constructor
    · rintro ⟨hxC, hxQ⟩
      obtain ⟨v, hv⟩ := mem_iUnion.mp (hDcover.symm ▸ hxQ)
      obtain ⟨b, _, hb⟩ := mem_iUnion₂.mp ((hinc i v).subset ⟨hxC, hv⟩)
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
    · intro hx
      have hb : ∃ b : Bool, x ∈ B (i, b) := by
        rcases hx with hx | hx
        · exact ⟨false, hx⟩
        · exact ⟨true, hx⟩
      obtain ⟨b, hb⟩ := hb
      have hh := (hinc i (ends i b)).symm.subset (mem_iUnion₂.mpr ⟨b, rfl, hb⟩)
      exact ⟨hh.1, hDcover ▸ mem_iUnion.mpr ⟨ends i b, hh.2⟩⟩
  have hQR : Q ⊆ R := hQeq ▸ sdiff_subset
  let j : C(Q, R) := ⟨Set.inclusion hQR, continuous_inclusion _⟩
  have hj : Function.Injective (ModTwoMayerVietoris.homologyMapOf j 1) :=
    cut_inclusion_homology_injective sS R Q O B W (fun i b => H (i, b))
      hQeq hQ.isClosed (fun i => (hO i).1)
      (fun i => (hO i).2.2.2.trans (inter_subset_right.trans interior_subset)) hCC hincQ hW
  have hzero : ModTwoMayerVietoris.homologyMapOf j 1 ≫
      ModTwoMayerVietoris.homologyMapOf q 1 = 0 :=
    CutGraph.cut_graph_homology_comp_zero R Q hQR D hactual ends q hqD 1 one_ne_zero
  have hvertices : ∀ v, ∃ x, (q x : CutGraph.Ambient (ConnectedComponents Q) κ) =
      CutGraph.vertex v := by
    intro v
    obtain ⟨x, hx⟩ := (hD v).2.2.1.nonempty
    have hxQ : x ∈ Q := (hD v).2.2.2.1 hx
    have hxR : x ∈ R := (hQeq.subset hxQ).1
    exact ⟨⟨x, hxR⟩, hqD v ⟨x, hxR⟩ hx⟩
  refine ⟨Q, hfinite, B, H, sB, O, D, ends, W, q, s, hQeq, hQ, hQPL, hO, hCC,
    hcover, houtside, hD, hDD, hDcover, hactual, hinc, hW, hcenter, hqD, hqC, hqs,
    CutGraph.sectionIncidenceHomology_injective ends q s hqs, ?_,
    CutGraph.edge_count_le_homology_rank_add_vertices ends q s hqs, ?_,
    j, (fun _ => rfl), hj, hzero, ?_⟩
  · intro hRc
    let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hRc
    exact CutGraph.connected_cycle_rank_of_vertices_reached ends q hvertices
  · intro hRc
    let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hRc
    exact CutGraph.connected_edge_count_le_homology_rank_add_vertices ends q s hvertices hqs
  · have hbound (hRc : IsConnected R) : Fintype.card κ + 1 +
        ∑ v, Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology (D v) 1) ≤
          Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
            Fintype.card (ConnectedComponents Q) := by
      let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hRc
      have hcycle := CutGraph.connected_cycle_rank_of_vertices_reached ends q hvertices
      have hbound := CutGraph.component_cycle_rank_le ends j q s hqs hj hzero
      have hsum := PLDomain.finrank_disjoint_components Q D (fun v => (hD v).1)
        (fun v => (hD v).2.1) hDD hDcover 1
      rw [hsum] at hbound
      omega
    refine ⟨hbound, fun hRc => ?_⟩
    have hcount := PLDomain.card_le_zero_homology_components_add_rank_sum D
      (fun v => (hD v).1) (fun v => (hD v).2.1) 1
    have := hbound hRc
    omega

end PoincareMT.M76
