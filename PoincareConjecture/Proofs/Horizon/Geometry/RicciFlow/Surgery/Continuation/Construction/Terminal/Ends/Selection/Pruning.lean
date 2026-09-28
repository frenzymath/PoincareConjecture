import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Selection.Laminar
import Mathlib.Order.Preorder.Finite









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.SurgeryEndCut

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {N P : EpsilonNeck g}

theorem tails_disjoint_or_subset_or_subset_of_core
    (C : SurgeryEndCut N) (D : SurgeryEndCut P)
    (connection : LeviCivitaData g) (rho : ℝ)
    (hneck : Disjoint N.carrier P.carrier)
    (hcore : N.center ∈ SurgeryTerminalCoreComponents connection rho)
    (hC : Disjoint {x | connection.scalarCurvature x ≤ rho⁻¹ ^ 2} (closure C.tail))
    (hD : Disjoint {x | connection.scalarCurvature x ≤ rho⁻¹ ^ 2} (closure D.tail)) :
    Disjoint C.tail D.tail ∨ C.tail ⊆ D.tail ∨ D.tail ⊆ C.tail := by
  by_cases hdis : Disjoint C.tail D.tail
  · exact Or.inl hdis
  obtain ⟨x, hxC, hxD⟩ := not_disjoint_iff.mp hdis
  obtain ⟨p, hp, hNp⟩ := hcore
  have hpN : p ∈ connectedComponent N.center := by
    rw [← connectedComponent_eq hNp]
    exact mem_connectedComponent
  have hcomp : connectedComponent N.center = connectedComponent P.center :=
    (connectedComponent_eq (C.tail_subset_component hxC)).trans
      (connectedComponent_eq (D.tail_subset_component hxD)).symm
  exact C.tails_disjoint_or_subset_or_subset D hneck
    ⟨hpN, disjoint_left.mp hC hp⟩ ⟨hcomp ▸ hpN, disjoint_left.mp hD hp⟩



theorem exists_disjoint_tail_subfamily {ι : Type v}
    (connection : LeviCivitaData g) (rho : ℝ)
    (N : ι → EpsilonNeck g) (cuts : ∀ i, SurgeryEndCut (N i)) (s : Finset ι)
    (hneck : (s : Set ι).Pairwise fun i j => Disjoint (N i).carrier (N j).carrier)
    (hcore : ∀ i ∈ s, (N i).center ∈ SurgeryTerminalCoreComponents connection rho)
    (havoid : ∀ i ∈ s, Disjoint {x | connection.scalarCurvature x ≤ rho⁻¹ ^ 2}
      (closure (cuts i).tail)) :
    ∃ t : Finset ι, t ⊆ s ∧
      (t : Set ι).Pairwise (fun i j => Disjoint (cuts i).tail (cuts j).tail) ∧
      (∀ i ∈ s, ∃ j ∈ t, (cuts i).tail ⊆ (cuts j).tail) ∧
      (⋃ i ∈ t, (cuts i).tail) = ⋃ i ∈ s, (cuts i).tail := by
  classical
  let t := s.filter fun i => Maximal (· ∈ s.image (fun j => (cuts j).tail)) (cuts i).tail
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (cuts i).tail ≠ (cuts j).tail := by
    intro i hi j hj hij heq
    have hs : (N i).central_sphere = (N j).central_sphere :=
      (cuts i).frontier_eq.symm.trans ((congrArg frontier heq).trans (cuts j).frontier_eq)
    exact disjoint_left.mp (hneck hi hj hij)
      ((N i).central_sphere_subset (N i).center_on_central_sphere)
      ((N j).central_sphere_subset (hs ▸ (N i).center_on_central_sphere))
  have hdis : (t : Set ι).Pairwise fun i j => Disjoint (cuts i).tail (cuts j).tail := by
    intro i hi j hj hij
    have his := hts hi
    have hjs := hts hj
    rcases (cuts i).tails_disjoint_or_subset_or_subset_of_core (cuts j) connection rho
      (hneck his hjs hij) (hcore i his) (havoid i his) (havoid j hjs) with h | h | h
    · exact h
    · exact False.elim (hdistinct i his j hjs hij
        ((Finset.mem_filter.mp hi).2.eq_of_subset (Finset.mem_image.mpr ⟨j, hjs, rfl⟩) h))
    · exact False.elim (hdistinct j hjs i his hij.symm
        ((Finset.mem_filter.mp hj).2.eq_of_subset (Finset.mem_image.mpr ⟨i, his, rfl⟩) h))
  have hcover : ∀ i ∈ s, ∃ j ∈ t, (cuts i).tail ⊆ (cuts j).tail := by
    intro i hi
    obtain ⟨V, hV, hmax⟩ := (s.image (fun j => (cuts j).tail)).exists_le_maximal
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    obtain ⟨j, hj, hjV⟩ := Finset.mem_image.mp hmax.1
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩, ?_⟩
    · simpa only [hjV] using hmax
    · simpa only [hjV] using hV
  refine ⟨t, hts, hdis, hcover, Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hts hi, hxi⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact mem_iUnion₂.mpr ⟨j, hj, hij hxi⟩

end PoincareConjecture.SurgeryEndCut
