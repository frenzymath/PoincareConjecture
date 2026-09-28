import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Endpoints
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Order
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.Prepend
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Distance.NewScale
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

theorem exists_prepend (C : BalancedNeckChain g ε) {a : ℤ}
    (ha : a ∈ C.shape.active) (hprev : a - 1 ∉ C.shape.active)
    (P S : EpsilonNeck g) (hselected : P.SameUpToReversal S)
    (he : P.epsilon = ε)
    (hfresh : ∀ i ∈ C.shape.active, P.center ≠ (C.neck i).center)
    (hoverlap : (P.carrier ∩ (C.neck a).carrier).Nonempty)
    (hquarters : P.region (ε⁻¹ / 2) ε⁻¹ ⊆ (C.neck a).carrier ∧
      (C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ P.carrier)
    (hwithin : P.carrier ∩ (C.neck a).carrier ⊆
      P.region (-ε⁻¹ / 2) ε⁻¹ ∩ (C.neck a).region (-ε⁻¹) (ε⁻¹ / 2))
    (hno : ∀ j ∈ C.shape.active, ∃ s ∈ Ioo (-ε⁻¹) 0,
      Disjoint (C.neck j).carrier (P.region (-ε⁻¹) s))
    (hdist : ENNReal.ofReal ((0.99 : ℝ) * P.scale * ε⁻¹) ≤
        g.edist P.center (C.neck a).center ∧
      g.edist P.center (C.neck a).center ≤
        ENNReal.ofReal ((1.01 : ℝ) * P.scale * ε⁻¹)) :
    ∃ D : BalancedNeckChain g ε,
      C.IsExtension D ∧ D.shape = C.shape.extendLeft ∧
      D.source_necks = insert S C.source_necks ∧ D.neck (a - 1) = P := by
  classical
  let J := C.shape.extendLeft
  have hJ : J.active = insert (a - 1) C.shape.active :=
    ChainShape.extendLeft_active ha hprev
  have hleft {i : ℤ} (hi : i ∈ C.shape.active) : a ≤ i :=
    ChainShape.le_of_left_endpoint ha hprev hi
  let N : ℤ → EpsilonNeck g := fun i => if i = a - 1 then P else C.neck i
  have hnew : N (a - 1) = P := if_pos rfl
  have hold (i : ℤ) (hi : i ∈ C.shape.active) : N i = C.neck i := by
    apply if_neg
    intro heq
    exact hprev (heq ▸ hi)
  have pair (i : ℤ) (hi : i ∈ J.active) (hj : i + 1 ∈ J.active) :
      (i = a - 1 ∧ i + 1 = a) ∨
        (i ∈ C.shape.active ∧ i + 1 ∈ C.shape.active) := by
    rw [hJ, mem_insert_iff] at hi hj
    rcases hi with rfl | hi
    · exact Or.inl ⟨rfl, by omega⟩
    · rcases hj with hj | hj
      · have := hleft hi
        omega
      · exact Or.inr ⟨hi, hj⟩
  let D : BalancedNeckChain g ε := {
    shape := J
    neck := N
    source_necks := insert S C.source_necks
    selected := by
      intro i hi
      rw [hJ, mem_insert_iff] at hi
      rcases hi with rfl | hi
      · exact ⟨S, mem_insert S _, hnew ▸ hselected⟩
      · obtain ⟨T, hT, hNT⟩ := C.selected i hi
        exact ⟨T, mem_insert_of_mem _ hT, hold i hi ▸ hNT⟩
    active_nonempty := ⟨a - 1, hJ ▸ mem_insert _ _⟩
    epsilon_eq := by
      intro i hi
      rw [hJ, mem_insert_iff] at hi
      rcases hi with rfl | hi
      · rwa [hnew]
      · rw [hold i hi]
        exact C.epsilon_eq i hi
    centers_distinct := by
      intro i hi j hj hij
      rw [hJ, mem_insert_iff] at hi hj
      rcases hi with rfl | hi <;> rcases hj with rfl | hj
      · exact (hij rfl).elim
      · rw [hnew, hold j hj]
        exact hfresh j hj
      · rw [hold i hi, hnew]
        exact (hfresh i hi).symm
      · rw [hold i hi, hold j hj]
        exact C.centers_distinct hi hj hij
    adjacent_overlap := by
      intro i hi hj
      rcases pair i hi hj with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [hi, hnew, show a - 1 + 1 = a by omega, hold a ha]
        exact hoverlap
      · rw [hold i hi, hold (i + 1) hj]
        exact C.adjacent_overlap i hi hj
    overlap_contains_quarters := by
      intro i hi hj
      rcases pair i hi hj with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [hi, hnew, show a - 1 + 1 = a by omega, hold a ha]
        exact hquarters
      · rw [hold i hi, hold (i + 1) hj]
        exact C.overlap_contains_quarters i hi hj
    overlap_within_three_quarters := by
      intro i hi hj
      rcases pair i hi hj with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [hi, hnew, show a - 1 + 1 = a by omega, hold a ha]
        exact hwithin
      · rw [hold i hi, hold (i + 1) hj]
        exact C.overlap_within_three_quarters i hi hj
    later_disjoint_negative_end := by
      intro i hi j hj hij
      rw [hJ, mem_insert_iff] at hi hj
      have hjold : j ∈ C.shape.active := by
        rcases hj with rfl | hj
        · rcases hi with rfl | hi
          · omega
          · have := hleft hi
            omega
        · exact hj
      rw [hold j hjold]
      rcases hi with rfl | hi
      · rw [hnew]
        exact hno j hjold
      · rw [hold i hi]
        exact C.later_disjoint_negative_end i hi j hjold hij
    balanced_center_distance := by
      intro i hi hj
      rcases pair i hi hj with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [hi, hnew, show a - 1 + 1 = a by omega, hold a ha]
        exact hdist
      · rw [hold i hi, hold (i + 1) hj]
        exact C.balanced_center_distance i hi hj }
  refine ⟨D, ⟨?_, subset_insert _ _, fun i hi => (hold i hi).symm⟩,
    rfl, rfl, hnew⟩
  intro i hi
  change i ∈ J.active
  rw [hJ]
  exact mem_insert_of_mem _ hi

theorem exists_prepend_at_outer_frontier_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
      ∀ (C : BalancedNeckChain g ε) (P S : EpsilonNeck g), ε ≤ ε₀ →
        P.epsilon = ε → P.SameUpToReversal S →
        ∀ a ∈ C.shape.active, a - 1 ∉ C.shape.active → (C.neck a).IsSeparating →
          P.center ∈ closure ((C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2)) →
          P.center ∉ C.unionOpen →
          P.region (ε⁻¹ / 2) ε⁻¹ ⊆ (C.neck a).carrier →
          (C.neck a).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ P.carrier →
          P.carrier ∩ (C.neck a).carrier ⊆
            P.region (-ε⁻¹ / 2) ε⁻¹ ∩ (C.neck a).region (-ε⁻¹) (ε⁻¹ / 2) →
          ∃ D : BalancedNeckChain g ε,
            C.IsExtension D ∧ D.shape = C.shape.extendLeft ∧
            D.source_necks = insert S C.source_necks ∧ D.neck (a - 1) = P := by
  obtain ⟨ε₁, hε₁, _, hnoreturn⟩ := exists_prepend_no_return_threshold.{u}
  obtain ⟨ε₂, hε₂, hsmall, hdist⟩ :=
    EpsilonNeck.exists_balanced_frontier_distance_in_new_scale.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_right _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C P S hε he hsame a ha hprev hsep
    hfront hout hpos hneg hwithin
  have heA := C.epsilon_eq a ha
  have hi : 0 < ε⁻¹ := inv_pos.mpr (he ▸ P.epsilon_pos)
  have houtA : P.center ∉ (C.neck a).carrier := by
    intro hx
    exact hout (mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩)
  have hfrontA : P.center ∈ frontier (C.neck a).carrier := by
    rw [(C.neck a).carrier_open.frontier_eq]
    exact ⟨closure_mono ((C.neck a).region_subset_carrier _ _) hfront, houtA⟩
  have hd := hdist (C.neck a) P (by simpa only [heA] using hε.trans (min_le_right _ _))
    (he.trans heA.symm) hfrontA
  have hoverlap : (P.carrier ∩ (C.neck a).carrier).Nonempty := by
    obtain ⟨x, hx⟩ := ((C.neck a).isConnected_region
      (a := -ε⁻¹) (b := -ε⁻¹ / 2) (by rw [heA])
      (by rw [heA]; linarith) (by linarith)).nonempty
    exact ⟨x, hneg hx, hx.1⟩
  apply C.exists_prepend ha hprev P S hsame he ?_ hoverlap ⟨hpos, hneg⟩ hwithin ?_
    (by simpa only [he] using hd)
  · intro i hi hcenter
    apply hout
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hcenter ▸
      (C.neck i).central_sphere_subset (C.neck i).center_on_central_sphere⟩
  · intro j hj
    exact ⟨-ε⁻¹ / 2, ⟨by linarith, by linarith⟩,
      hnoreturn C P (hε.trans (min_le_left _ _)) he a ha hsep hneg hwithin j hj
        (ChainShape.le_of_left_endpoint ha hprev hj)⟩

end PoincareConjecture.BalancedNeckChain
