import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.CircleComponents



noncomputable section
set_option autoImplicit false
open Set Metric Function

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

variable {I J X : Type*} [Finite I] [Finite J] [TopologicalSpace X] [T2Space X]



theorem finite_circle_ranges_eq_of_common_point
    (C : I → S1 → X) (D : J → S1 → X)
    (hC : ∀ i, Continuous (C i)) (hD : ∀ j, Continuous (D j))
    (hCdis : Pairwise (fun i j => Disjoint (range (C i)) (range (C j))))
    (hDdis : Pairwise (fun i j => Disjoint (range (D i)) (range (D j))))
    (hunion : (⋃ i, range (C i)) = ⋃ j, range (D j))
    {i : I} {j : J} {x : X} (hxC : x ∈ range (C i)) (hxD : x ∈ range (D j)) :
    range (C i) = range (D j) := by
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)
  have hCi := Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover
    (fun k => range (C k)) (fun k => (isCompact_range (hC k)).isClosed)
    (fun k => isPreconnected_range (hC k)) hCdis rfl hxC
  have hDj := Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover
    (fun k => range (D k)) (fun k => (isCompact_range (hD k)).isClosed)
    (fun k => isPreconnected_range (hD k)) hDdis hunion.symm hxD
  exact hCi.symm.trans hDj




theorem exists_finite_circle_range_equiv
    (C : I → S1 → X) (D : J → S1 → X)
    (hC : ∀ i, Continuous (C i)) (hD : ∀ j, Continuous (D j))
    (hCdis : Pairwise (fun i j => Disjoint (range (C i)) (range (C j))))
    (hDdis : Pairwise (fun i j => Disjoint (range (D i)) (range (D j))))
    (hunion : (⋃ i, range (C i)) = ⋃ j, range (D j)) :
    ∃ E : I ≃ J, ∀ i, range (C i) = range (D (E i)) := by
  classical
  let q : S1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hm (i : I) : ∃ j, C i q ∈ range (D j) :=
    mem_iUnion.mp (hunion.subset (mem_iUnion_of_mem i (mem_range_self q)))
  choose j hj using hm
  have heq (i : I) : range (C i) = range (D (j i)) :=
    finite_circle_ranges_eq_of_common_point C D hC hD hCdis hDdis hunion
      (mem_range_self q) (hj i)
  have hji : Injective j := by
    intro i k hik
    have hEq : range (C i) = range (C k) := by rw [heq i, heq k, hik]
    by_contra hne
    exact disjoint_left.mp (hCdis hne)
      (mem_range_self q) (hEq.subset (mem_range_self q))
  have hjs : Surjective j := by
    intro k
    obtain ⟨i, hi⟩ := mem_iUnion.mp
      (hunion.superset (mem_iUnion_of_mem k (mem_range_self q)))
    refine ⟨i, ?_⟩
    by_contra hne
    exact disjoint_left.mp (hDdis hne) ((heq i).subset hi) (mem_range_self q)
  exact ⟨Equiv.ofBijective j ⟨hji, hjs⟩, heq⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
