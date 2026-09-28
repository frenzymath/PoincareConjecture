import PoincareConjecture.Proofs.Horizon.Topology.Connected.FourContacts.Resolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected



noncomputable section
set_option autoImplicit false

open Set Metric Function

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem pairwise_disjoint_ranges (C : Fin 2 → S1 → E2)
    (hC : Disjoint (range (C 0)) (range (C 1))) :
    Pairwise (fun i j => Disjoint (range (C i)) (range (C j))) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hC
  · exact hC.symm
  · exact (hij rfl).elim

private theorem circle_ranges_eq_of_common_point
    (C D : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i)) (hD : ∀ i, Continuous (D i))
    (hCdis : Disjoint (range (C 0)) (range (C 1)))
    (hDdis : Disjoint (range (D 0)) (range (D 1)))
    (hunion : (⋃ i, range (C i)) = ⋃ i, range (D i))
    {i j : Fin 2} {x : E2} (hxC : x ∈ range (C i)) (hxD : x ∈ range (D j)) :
    range (C i) = range (D j) := by
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)
  have hCi := Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover
    (fun k => range (C k)) (fun k => (isCompact_range (hC k)).isClosed)
    (fun k => isPreconnected_range (hC k)) (pairwise_disjoint_ranges C hCdis) rfl hxC
  have hDj := Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover
    (fun k => range (D k)) (fun k => (isCompact_range (hD k)).isClosed)
    (fun k => isPreconnected_range (hD k)) (pairwise_disjoint_ranges D hDdis) hunion.symm hxD
  exact hCi.symm.trans hDj



theorem circle_pair_ranges_eq_of_union_eq_of_inter_nonempty
    (C D : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i)) (hD : ∀ i, Continuous (D i))
    (hCdis : Disjoint (range (C 0)) (range (C 1)))
    (hDdis : Disjoint (range (D 0)) (range (D 1)))
    (hunion : (⋃ i, range (C i)) = ⋃ i, range (D i))
    (hmeet : ∀ i, (range (C i) ∩ range (D i)).Nonempty) :
    ∀ i, range (C i) = range (D i) := by
  intro i
  obtain ⟨x, hxC, hxD⟩ := hmeet i
  exact circle_ranges_eq_of_common_point C D hC hD hCdis hDdis hunion hxC hxD



theorem exists_circle_pair_range_permutation
    (C D : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i)) (hD : ∀ i, Continuous (D i))
    (hCdis : Disjoint (range (C 0)) (range (C 1)))
    (hDdis : Disjoint (range (D 0)) (range (D 1)))
    (hunion : (⋃ i, range (C i)) = ⋃ i, range (D i)) :
    ∃ E : Equiv.Perm (Fin 2), ∀ i, range (C i) = range (D (E i)) := by
  classical
  let q : S1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hm (i : Fin 2) : ∃ j, C i q ∈ range (D j) :=
    mem_iUnion.mp (hunion.subset (mem_iUnion_of_mem i (mem_range_self q)))
  choose j hj using hm
  have heq (i : Fin 2) : range (C i) = range (D (j i)) :=
    circle_ranges_eq_of_common_point C D hC hD hCdis hDdis hunion (mem_range_self q) (hj i)
  have hji : Injective j := by
    intro i k hik
    have hEq : range (C i) = range (C k) := by rw [heq i, heq k, hik]
    by_contra hne
    exact disjoint_left.mp (pairwise_disjoint_ranges C hCdis hne)
      (mem_range_self q) (hEq.subset (mem_range_self q))
  exact ⟨Equiv.ofBijective j ((Fintype.bijective_iff_injective_and_card j).mpr ⟨hji, rfl⟩), heq⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
