import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InfiniteFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InnerSlabCover
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InteriorThickness
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture

theorem ChainShape.finite_end_indices (shape : ChainShape) :
    {i | i ∈ shape.active ∧ (i - 1 ∉ shape.active ∨ i + 1 ∉ shape.active)}.Finite := by
  cases shape with
  | finite a b =>
    apply ((finite_singleton b).insert a).subset
    intro i hi
    simp only [ChainShape.active, mem_ofPred_eq, mem_Icc] at hi
    simp only [mem_insert_iff, mem_singleton_iff]
    omega
  | forward a =>
    apply (finite_singleton a).subset
    intro i hi
    simp only [ChainShape.active, mem_ofPred_eq, mem_Ici] at hi
    simp only [mem_singleton_iff]
    omega
  | backward b =>
    apply (finite_singleton b).subset
    intro i hi
    simp only [ChainShape.active, mem_ofPred_eq, mem_Iic] at hi
    simp only [mem_singleton_iff]
    omega
  | biInfinite => simp [ChainShape.active]

namespace BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε)

local notation "slab(" N ")" => EpsilonNeck.coordinate_map N ''
  (Set.prod univ (Icc (-(3 / 4 : ℝ) * (EpsilonNeck.epsilon N)⁻¹)
    ((3 / 4 : ℝ) * (EpsilonNeck.epsilon N)⁻¹)))

theorem frontier_subset_iUnion_closure_of_quarter_capture
    (hcapture : ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      (C.neck i).region (ε⁻¹ / 2) ε⁻¹ ⊆ slab(C.neck (i + 1)) ∨
      (C.neck (i + 1)).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ slab(C.neck i)) :
    frontier (C.unionOpen : Set M) ⊆
      ⋃ i : {i // i ∈ C.shape.active}, closure (C.neck i.1).carrier := by
  obtain ⟨i₀, hi₀⟩ := C.active_nonempty
  have hepos : 0 < ε := C.epsilon_eq i₀ hi₀ ▸ (C.neck i₀).epsilon_pos
  have hinv := inv_pos.mpr hepos
  let r : ℝ := (7 / 8 : ℝ) * ε⁻¹
  let core : Set M := ⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).region (-r) r
  let ends : Set ℤ :=
    {i | i ∈ C.shape.active ∧ (i - 1 ∉ C.shape.active ∨ i + 1 ∉ C.shape.active)}
  have hends : ends.Finite := C.shape.finite_end_indices
  have hcore : closure core ⊆ (C.unionOpen : Set M) :=
    EpsilonNeck.closure_iUnion_region_subset (fun i : {i // i ∈ C.shape.active} => C.neck i.1)
      (fun i => C.epsilon_eq i.1 i.2) (by dsimp [r]; positivity)
      (by dsimp [r]; linarith)
  have hcover : (C.unionOpen : Set M) ⊆ core ∪ ⋃ i ∈ ends, (C.neck i).carrier := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rcases C.mem_inner_slab_or_missing_neighbor_quarter hcapture i.2 hxi with
      ⟨j, hj, hxj⟩ | ⟨hprev, _⟩ | ⟨hnext, _⟩
    · apply Or.inl
      apply mem_iUnion.mpr
      refine ⟨⟨j, hj⟩, ?_⟩
      obtain ⟨z, hz, rfl⟩ := hxj
      have he := C.epsilon_eq j hj
      have hlow := hz.2.1
      have hhigh := hz.2.2
      rw [he] at hlow hhigh
      have hzdom : z ∈ (C.neck j).cylinderDomain := by
        refine ⟨mem_univ _, ?_⟩
        rw [he]
        constructor <;> linarith
      refine ⟨(C.neck j).coordinate_map_mem hzdom, ?_⟩
      rw [(C.neck j).coordinate_inverse_coordinate_map hzdom]
      dsimp [r]
      constructor <;> linarith
    · exact Or.inr (mem_iUnion₂.mpr ⟨i.1, ⟨i.2, Or.inl hprev⟩, hxi⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i.1, ⟨i.2, Or.inr hnext⟩, hxi⟩)
  intro x hx
  have hout : x ∉ (C.unionOpen : Set M) := (C.unionOpen.isOpen.frontier_eq ▸ hx).2
  have hc := closure_mono hcover (frontier_subset_closure hx)
  rw [closure_union, hends.closure_biUnion] at hc
  rcases hc with hc | hc
  · exact (hout (hcore hc)).elim
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hc
    exact mem_iUnion.mpr ⟨⟨i, hi.1⟩, hxi⟩

theorem frontier_subset_outer_ends_of_quarter_capture
    (hcapture : ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      (C.neck i).region (ε⁻¹ / 2) ε⁻¹ ⊆ slab(C.neck (i + 1)) ∨
      (C.neck (i + 1)).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ slab(C.neck i)) :
    frontier (C.unionOpen : Set M) ⊆
      match C.shape with
      | .finite a b => closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2)) ∪
          closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹)
      | .forward a => closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2))
      | .backward b => closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹)
      | .biInfinite => ∅ := by
  intro x hx
  exact C.frontier_inter_iUnion_closure_subset_outer_ends
    ⟨hx, C.frontier_subset_iUnion_closure_of_quarter_capture hcapture hx⟩

end BalancedNeckChain

end PoincareConjecture
