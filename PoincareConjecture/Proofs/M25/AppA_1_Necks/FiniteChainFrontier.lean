import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem frontier_finite_union_subset_end_closures
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (C : BalancedNeckChain g epsilon) {a b : ℤ}
    (hshape : C.shape = ChainShape.finite a b)
    (hquarters : ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      closure ((C.neck i).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
          (C.neck (i + 1)).carrier ∧
        closure ((C.neck (i + 1)).region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆
          (C.neck i).carrier) :
    frontier (⋃ i ∈ C.shape.active, (C.neck i).carrier) ⊆
      closure ((C.neck a).region (-epsilon⁻¹) 0) ∪
        closure ((C.neck b).region 0 epsilon⁻¹) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hfinite : C.shape.active.Finite := by
    rw [hshape]
    exact Set.finite_Icc a b
  have hopen : IsOpen (⋃ i ∈ C.shape.active, (C.neck i).carrier) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  intro x hx
  rw [hopen.frontier_eq] at hx
  have hxclosure := hx.1
  rw [hfinite.closure_biUnion] at hxclosure
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxclosure
  obtain ⟨hai, hib⟩ := (hactive i).mp hi
  have he : (C.neck i).epsilon = epsilon := C.epsilon_eq i hi
  have hepos : 0 < epsilon := he ▸ (C.neck i).epsilon_pos
  have hL : 0 < epsilon⁻¹ := inv_pos.mpr hepos
  have hout (j : ℤ) (hj : j ∈ C.shape.active) : x ∉ (C.neck j).carrier := by
    intro hxj
    exact hx.2 (mem_iUnion₂.mpr ⟨j, hj, hxj⟩)
  let K := (C.neck i).coordinate_map ''
    (univ ×ˢ Icc (-epsilon⁻¹ / 2) (epsilon⁻¹ / 2))
  have hKclosed : IsClosed K := by
    apply ((C.neck i).isCompact_coordinate_slab ?_ ?_).isClosed
    · rw [he]
      linarith
    · rw [he]
      linarith
  have hKsub : K ⊆ (C.neck i).carrier := by
    rintro y ⟨z, hz, rfl⟩
    apply (C.neck i).coordinate_map_mem
    refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [he] <;> linarith [hz.2.1, hz.2.2]
  have hcover : (C.neck i).carrier ⊆
      K ∪ (C.neck i).region (-epsilon⁻¹) (-epsilon⁻¹ / 2) ∪
        (C.neck i).region (epsilon⁻¹ / 2) epsilon⁻¹ := by
    intro y hy
    have hycoord := ((C.neck i).coordinate_inverse_mem y hy).2
    rw [he] at hycoord
    by_cases hneg : ((C.neck i).coordinate_inverse y).2 < -epsilon⁻¹ / 2
    · exact Or.inl (Or.inr ⟨hy, hycoord.1, hneg⟩)
    by_cases hpos : epsilon⁻¹ / 2 < ((C.neck i).coordinate_inverse y).2
    · exact Or.inr ⟨hy, hpos, hycoord.2⟩
    exact Or.inl (Or.inl ⟨(C.neck i).coordinate_inverse y,
      ⟨mem_univ _, le_of_not_gt hneg, le_of_not_gt hpos⟩,
      (C.neck i).coordinate_map_inverse hy⟩)
  have hxparts := closure_mono hcover hxi
  rw [closure_union, closure_union, hKclosed.closure_eq] at hxparts
  rcases hxparts with (hxK | hxneg) | hxpos
  · exact (hout i hi (hKsub hxK)).elim
  · have hia : i = a := by
      by_contra hne
      have hprev : i - 1 ∈ C.shape.active :=
        (hactive _).mpr (by constructor <;> omega)
      have hnext : i - 1 + 1 ∈ C.shape.active := by simpa using hi
      have hsub := (hquarters (i - 1) hprev hnext).2
      have hxprev : x ∈ (C.neck (i - 1)).carrier :=
        hsub (by simpa using hxneg)
      exact hout (i - 1) hprev hxprev
    left
    rw [hia] at hxneg
    have hsub : (C.neck a).region (-epsilon⁻¹) (-epsilon⁻¹ / 2) ⊆
        (C.neck a).region (-epsilon⁻¹) 0 := by
      intro y hy
      exact ⟨hy.1, hy.2.1, by linarith [hy.2.2]⟩
    exact closure_mono hsub hxneg
  · have hib : i = b := by
      by_contra hne
      have hnext : i + 1 ∈ C.shape.active :=
        (hactive _).mpr (by constructor <;> omega)
      exact hout (i + 1) hnext ((hquarters i hi hnext).1 hxpos)
    right
    rw [hib] at hxpos
    have hsub : (C.neck b).region (epsilon⁻¹ / 2) epsilon⁻¹ ⊆
        (C.neck b).region 0 epsilon⁻¹ := by
      intro y hy
      exact ⟨hy.1, by linarith [hy.2.1], hy.2.2⟩
    exact closure_mono hsub hxpos

theorem exists_exterior_end_center_of_not_subset
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (H : NeckOnlyCover g) (C : BalancedNeckChain g H.epsilon)
    {a b : ℤ} (hshape : C.shape = ChainShape.finite a b)
    (hquarters : ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      closure ((C.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) ⊆
          (C.neck (i + 1)).carrier ∧
        closure ((C.neck (i + 1)).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ⊆
          (C.neck i).carrier)
    (hsource : C.source_necks = H.necks)
    (hmeet : (H.X ∩ (⋃ i ∈ C.shape.active, (C.neck i).carrier)).Nonempty)
    (hnot : ¬ H.X ⊆ ⋃ i ∈ C.shape.active, (C.neck i).carrier) :
    ∃ N' : EpsilonNeck g,
      N' ∈ C.source_necks ∧ N'.epsilon = H.epsilon ∧
      N'.center ∈ H.X ∧
      N'.center ∉ (⋃ i ∈ C.shape.active, (C.neck i).carrier) ∧
      (N'.center ∈ closure ((C.neck a).region (-H.epsilon⁻¹) 0) ∨
        N'.center ∈ closure ((C.neck b).region 0 H.epsilon⁻¹)) := by
  classical
  have hopen : IsOpen (⋃ i ∈ C.shape.active, (C.neck i).carrier) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  have hescape : ¬ closure (⋃ i ∈ C.shape.active, (C.neck i).carrier) ∩ H.X ⊆
      ⋃ i ∈ C.shape.active, (C.neck i).carrier := by
    intro hsub
    exact hnot (H.connected_X.2.subset_of_closure_inter_subset hopen hmeet hsub)
  obtain ⟨y, hy, hyout⟩ := Set.not_subset.mp hescape
  have hyfront : y ∈ frontier (⋃ i ∈ C.shape.active, (C.neck i).carrier) := by
    rw [hopen.frontier_eq]
    exact ⟨hy.1, hyout⟩
  have hyend := C.frontier_finite_union_subset_end_closures hshape hquarters hyfront
  obtain ⟨N', hN', hcenter⟩ := H.pointwise_center_cover y hy.2
  refine ⟨N', hsource.symm ▸ hN', H.neck_epsilon N' hN', ?_, ?_, ?_⟩
  · simpa only [hcenter] using hy.2
  · simpa only [hcenter] using hyout
  · simpa only [hcenter, mem_union] using hyend

end PoincareConjecture.BalancedNeckChain
