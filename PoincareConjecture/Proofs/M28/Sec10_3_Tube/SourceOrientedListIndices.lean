import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceOrientedList
import Mathlib.Data.List.GetD








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.SourceOrientedList

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
  {S : CounterexampleNeckSegment E}


def active (L : SourceOrientedList S) : Set ℤ := Icc 0 (L.nodes.length - 1)



def node (L : SourceOrientedList S) (i : ℤ) : ℝ × EpsilonNeck (E.flow.metric E.time) :=
  L.nodes.getD i.toNat (L.nodes.head L.nonempty)

theorem active_nonempty (L : SourceOrientedList S) : L.active.Nonempty := by
  have hlen : 0 < L.nodes.length := List.length_pos_iff.mpr L.nonempty
  refine ⟨0, ?_⟩
  simp only [active, mem_Icc]
  constructor <;> omega

theorem toNat_lt_length (L : SourceOrientedList S) {i : ℤ} (hi : i ∈ L.active) :
    i.toNat < L.nodes.length := by
  change 0 ≤ i ∧ i ≤ (L.nodes.length : ℤ) - 1 at hi
  omega

theorem node_eq_getElem (L : SourceOrientedList S) {i : ℤ} (hi : i ∈ L.active) :
    L.node i = L.nodes[i.toNat]'(L.toNat_lt_length hi) :=
  List.getD_eq_getElem _ _ (L.toNat_lt_length hi)

theorem node_mem (L : SourceOrientedList S) {i : ℤ} (hi : i ∈ L.active) :
    L.node i ∈ L.nodes := by
  rw [L.node_eq_getElem hi]
  exact List.getElem_mem _

theorem node_time_mem (L : SourceOrientedList S) {i : ℤ} (hi : i ∈ L.active) :
    (L.node i).1 ∈ Icc S.lower S.upper :=
  (L.vertex _ (L.node_mem hi)).1

theorem node_provenance (L : SourceOrientedList S) {i : ℤ} (hi : i ∈ L.active) :
    ∃ N ∈ S.cover.necks,
      ((L.node i).2 = N ∨ (L.node i).2 = N.reversed) ∧
        S.path (L.node i).1 = (L.node i).2.center :=
  (L.vertex _ (L.node_mem hi)).2

theorem node_epsilon (L : SourceOrientedList S) {i : ℤ} (hi : i ∈ L.active) :
    (L.node i).2.epsilon = epsilon := by
  obtain ⟨N, hN, hchoice, _⟩ := L.node_provenance hi
  have h := (S.cover.neck_epsilon N hN).trans S.cover_epsilon
  rcases hchoice with hN | hN <;>
    simpa only [hN, EpsilonNeck.reversed_epsilon] using h

theorem node_center (L : SourceOrientedList S) {i : ℤ} (hi : i ∈ L.active) :
    S.path (L.node i).1 = (L.node i).2.center := by
  obtain ⟨_, _, _, h⟩ := L.node_provenance hi
  exact h

theorem node_time_lt (L : SourceOrientedList S) {i j : ℤ}
    (hi : i ∈ L.active) (hj : j ∈ L.active) (hij : i < j) :
    (L.node i).1 < (L.node j).1 := by
  let R : (ℝ × EpsilonNeck (E.flow.metric E.time)) →
      (ℝ × EpsilonNeck (E.flow.metric E.time)) → Prop := fun p q => p.1 < q.1
  let : Trans R R R := ⟨fun h₁ h₂ => h₁.trans h₂⟩
  have hchain : L.nodes.IsChain R := L.edges.imp (fun _ _ h => h.1)
  have hpair : L.nodes.Pairwise R := List.isChain_iff_pairwise.mp hchain
  have hnat : i.toNat < j.toNat := by
    have := hi.1
    omega
  have h := List.pairwise_iff_getElem.mp hpair i.toNat j.toNat
    (L.toNat_lt_length hi) (L.toNat_lt_length hj) hnat
  simpa only [L.node_eq_getElem hi, L.node_eq_getElem hj] using h

theorem node_edge (L : SourceOrientedList S) {i : ℤ}
    (hi : i ∈ L.active) (hnext : i + 1 ∈ L.active) :
    ∃ P ∈ S.cover.necks,
      SourceEdgeCommonOrientationPacket (L.node i).2 P (L.node (i + 1)).2
        (γ := S.path) (L.node i).1 (L.node (i + 1)).1 ∧
      SourceEdgePacket (L.node i).2 (L.node (i + 1)).2 epsilon := by
  have hnextNat : (i + 1).toNat = i.toNat + 1 := by
    have := hi.1
    omega
  have h := List.isChain_iff_getElem.mp L.edges i.toNat
    (by simpa only [hnextNat] using L.toNat_lt_length hnext)
  have h' : (L.node i).1 < (L.node (i + 1)).1 ∧
      ∃ P ∈ S.cover.necks,
        SourceEdgeCommonOrientationPacket (L.node i).2 P (L.node (i + 1)).2
          (γ := S.path) (L.node i).1 (L.node (i + 1)).1 ∧
        SourceEdgePacket (L.node i).2 (L.node (i + 1)).2 epsilon := by
    simpa only [L.node_eq_getElem hi, L.node_eq_getElem hnext, hnextNat] using h
  exact h'.2

theorem neckOfList_eq_node (L : SourceOrientedList S) (i : ℤ) :
    neckOfList (L.nodes.map Prod.snd) (L.nodes.head L.nonempty).2 i = (L.node i).2 := by
  exact List.getD_map _ _ _

end PoincareConjecture.M28.SourceOrientedList
