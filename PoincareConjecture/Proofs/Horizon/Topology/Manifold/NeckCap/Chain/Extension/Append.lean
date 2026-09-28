import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.Endpoint
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.BalancedDistance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Order
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Endpoints

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_append_at_outer_frontier_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
      ∀ (C : BalancedNeckChain g ε) (N S : EpsilonNeck g), ε ≤ ε₀ →
        N.epsilon = ε → N.SameUpToReversal S →
        (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ b ∈ C.shape.active, b + 1 ∉ C.shape.active →
          N.center ∈ closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹) →
          N.center ∉ C.unionOpen →
          (C.neck b).region (ε⁻¹ / 2) ε⁻¹ ⊆ N.carrier →
          N.region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ (C.neck b).carrier →
          (C.neck b).carrier ∩ N.carrier ⊆
            (C.neck b).region (-ε⁻¹ / 2) ε⁻¹ ∩ N.region (-ε⁻¹) (ε⁻¹ / 2) →
          ∃ D : BalancedNeckChain g ε,
            D.shape = C.shape.extendRight ∧ C.IsExtension D ∧
            D.source_necks = insert S C.source_necks ∧ D.neck (b + 1) = N ∧
            (D.unionOpen : Set M) = (C.unionOpen : Set M) ∪ N.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, hnoreturn⟩ := exists_outer_frontier_no_return_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C N S hε heq hsame hsep b hb hnext
    hfront hout hpos hneg hwithin
  classical
  let shape := C.shape.extendRight
  have hshape : shape.active = insert (b + 1) C.shape.active :=
    ChainShape.extendRight_active hb hnext
  have hmax (i : ℤ) (hi : i ∈ C.shape.active) : i ≤ b :=
    ChainShape.le_of_right_endpoint hb hnext hi
  let F : ℤ → EpsilonNeck g := fun i => if i = b + 1 then N else C.neck i
  have hFnew : F (b + 1) = N := by simp [F]
  have hFold (i : ℤ) (hi : i ∈ C.shape.active) : F i = C.neck i := by
    have hne : i ≠ b + 1 := by have := hmax i hi; omega
    simp [F, hne]
  have hmem (i : ℤ) : i ∈ shape.active ↔ i = b + 1 ∨ i ∈ C.shape.active := by
    rw [hshape, mem_insert_iff]
  have hnewmax (i : ℤ) (hi : i ∈ shape.active) : i ≤ b + 1 := by
    rcases (hmem i).mp hi with rfl | hi
    · exact le_rfl
    · have := hmax i hi; omega
  have hadj (i : ℤ) (hi : i ∈ shape.active) (hj : i + 1 ∈ shape.active) :
      i ∈ C.shape.active ∧ (i = b ∨ i + 1 ∈ C.shape.active) := by
    have hiold : i ∈ C.shape.active := by
      rcases (hmem i).mp hi with h | h
      · have := hnewmax (i + 1) hj; omega
      · exact h
    refine ⟨hiold, ?_⟩
    rcases (hmem (i + 1)).mp hj with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  have hεpos : 0 < ε := heq ▸ N.epsilon_pos
  have hεb := C.epsilon_eq b hb
  have hfrontb : N.center ∈ frontier (C.neck b).carrier := by
    rw [(C.neck b).carrier_open.frontier_eq]
    refine ⟨closure_mono ((C.neck b).region_subset_carrier _ _) hfront, ?_⟩
    intro hx
    exact hout (mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩)
  have hbalanced := (C.neck b).balanced_edist_of_mem_frontier
    (by simpa only [hεb] using hε.trans hsmall) hfrontb
  have hfresh (i : ℤ) (hi : i ∈ C.shape.active) : N.center ≠ (C.neck i).center := by
    intro he
    apply hout
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, he ▸
      (C.neck i).central_sphere_subset (C.neck i).center_on_central_sphere⟩
  have hnewavoid (i : ℤ) (hi : i ∈ C.shape.active) :
      Disjoint N.carrier ((C.neck i).region (-ε⁻¹) (-ε⁻¹ / 2)) :=
    hnoreturn C N hε heq hsep b hb hfront hout i hi (hmax i hi)
  have hoverlap : ((C.neck b).carrier ∩ N.carrier).Nonempty := by
    obtain ⟨x, hx⟩ := ((C.neck b).isConnected_region
      (a := ε⁻¹ / 2) (b := ε⁻¹) (by rw [hεb]; have := inv_pos.mpr hεpos; linarith)
      (by rw [hεb]) (by have := inv_pos.mpr hεpos; linarith)).nonempty
    exact ⟨x, hx.1, hpos hx⟩
  let D : BalancedNeckChain g ε := {
    shape := shape
    neck := F
    source_necks := insert S C.source_necks
    selected := by
      intro i hi
      rcases (hmem i).mp hi with rfl | hi
      · exact ⟨S, Or.inl rfl, hFnew ▸ hsame⟩
      · obtain ⟨T, hT, hs⟩ := C.selected i hi
        exact ⟨T, mem_insert_of_mem _ hT, hFold i hi ▸ hs⟩
    active_nonempty := ⟨b + 1, (hmem _).mpr (Or.inl rfl)⟩
    epsilon_eq := by
      intro i hi
      rcases (hmem i).mp hi with rfl | hi
      · rw [hFnew]; exact heq
      · rw [hFold i hi]; exact C.epsilon_eq i hi
    centers_distinct := by
      intro i hi j hj hij
      rcases (hmem i).mp hi with rfl | hi
      · rcases (hmem j).mp hj with rfl | hj
        · exact (hij rfl).elim
        · rw [hFnew, hFold j hj]; exact hfresh j hj
      · rcases (hmem j).mp hj with rfl | hj
        · rw [hFold i hi, hFnew]; exact (hfresh i hi).symm
        · rw [hFold i hi, hFold j hj]; exact C.centers_distinct hi hj hij
    adjacent_overlap := by
      intro i hi hj
      obtain ⟨hi, rfl | hj⟩ := hadj i hi hj
      · rw [hFold i hi, hFnew]; exact hoverlap
      · rw [hFold i hi, hFold (i + 1) hj]; exact C.adjacent_overlap i hi hj
    overlap_contains_quarters := by
      intro i hi hj
      obtain ⟨hi, rfl | hj⟩ := hadj i hi hj
      · rw [hFold i hi, hFnew]; exact ⟨hpos, hneg⟩
      · rw [hFold i hi, hFold (i + 1) hj]; exact C.overlap_contains_quarters i hi hj
    overlap_within_three_quarters := by
      intro i hi hj
      obtain ⟨hi, rfl | hj⟩ := hadj i hi hj
      · rw [hFold i hi, hFnew]; exact hwithin
      · rw [hFold i hi, hFold (i + 1) hj]; exact C.overlap_within_three_quarters i hi hj
    later_disjoint_negative_end := by
      intro i hi j hj hij
      have hiold : i ∈ C.shape.active := by
        rcases (hmem i).mp hi with h | h
        · have := hnewmax j hj; omega
        · exact h
      rw [hFold i hiold]
      rcases (hmem j).mp hj with rfl | hj
      · rw [hFnew]
        exact ⟨-ε⁻¹ / 2, ⟨by have := inv_pos.mpr hεpos; linarith,
          by have := inv_pos.mpr hεpos; linarith⟩, hnewavoid i hiold⟩
      · rw [hFold j hj]
        exact C.later_disjoint_negative_end i hiold j hj hij
    balanced_center_distance := by
      intro i hi hj
      obtain ⟨hi, rfl | hj⟩ := hadj i hi hj
      · rw [hFold i hi, hFnew]; simpa only [hεb] using hbalanced
      · rw [hFold i hi, hFold (i + 1) hj]; exact C.balanced_center_distance i hi hj }
  refine ⟨D, rfl, ⟨?_, subset_insert _ _, ?_⟩, rfl, hFnew, ?_⟩
  · intro i hi
    exact (hmem i).mpr (Or.inr hi)
  · intro i hi
    exact (hFold i hi).symm
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rcases (hmem i.1).mp i.2 with h | h
      · exact Or.inr (by simpa only [D, h, hFnew] using hi)
      · exact Or.inl (mem_iUnion.mpr ⟨⟨i.1, h⟩,
          by simpa only [D, hFold i.1 h] using hi⟩)
    · rintro (hx | hx)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨⟨i.1, (hmem i.1).mpr (Or.inr i.2)⟩,
          by simpa only [D, hFold i.1 i.2] using hi⟩
      · exact mem_iUnion.mpr ⟨⟨b + 1, (hmem _).mpr (Or.inl rfl)⟩,
          by simpa only [D, hFnew] using hx⟩

end PoincareConjecture.BalancedNeckChain
