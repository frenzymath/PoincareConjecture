import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InteriorCapture
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal
















set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

local notation "slab(" N ")" => EpsilonNeck.coordinate_map N ''
  (Set.prod univ (Icc (-(3 / 4 : ℝ) * (EpsilonNeck.epsilon N)⁻¹)
    ((3 / 4 : ℝ) * (EpsilonNeck.epsilon N)⁻¹)))

namespace EpsilonNeck

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem mem_inner_slab_iff (N : EpsilonNeck g) {x : M} :
    x ∈ slab(N) ↔ x ∈ N.carrier ∧
      -(3 / 4 : ℝ) * N.epsilon⁻¹ ≤ (N.coordinate_inverse x).2 ∧
        (N.coordinate_inverse x).2 ≤ (3 / 4 : ℝ) * N.epsilon⁻¹ := by
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  exact N.mem_coordinate_slab_iff (by linarith) (by linarith)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem reversed_inner_slab (N : EpsilonNeck g) :
    slab(N.reversed) = slab(N) := by
  ext x
  rw [mem_inner_slab_iff, mem_inner_slab_iff]
  simp only [reversed_carrier, reversed_epsilon, reversed_coordinate_inverse]
  constructor <;> rintro ⟨hx, h₁, h₂⟩ <;> refine ⟨hx, ?_, ?_⟩ <;> linarith



theorem negative_quarter_subset_frontier_neck_inner_slab
    (N N' : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : N'.epsilon = N.epsilon)
    (hscale : (0.99 : ℝ) * N.scale ≤ N'.scale)
    (hcenter : N'.center ∈ closure (N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2))) :
    N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆ slab(N') := by
  have h := N.reversed.positive_quarter_subset_frontier_neck_inner_slab N'.reversed
    hε heq hscale (by simpa only [reversed_center, reversed_region,
      reversed_epsilon, neg_div] using hcenter)
  have h' := h.trans (reversed_inner_slab N').subset
  simpa only [reversed_region, reversed_epsilon, neg_div] using h'

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in


theorem overlap_subset_inner_slabs_of_quarter_capture (N N' : EpsilonNeck g)
    (hwithin : N.carrier ∩ N'.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        N'.region (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2))
    (hcapture :
      N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ slab(N') ∨
      N'.region (-N'.epsilon⁻¹) (-N'.epsilon⁻¹ / 2) ⊆ slab(N)) :
    N.carrier ∩ N'.carrier ⊆ slab(N) ∪ slab(N') := by
  intro x hx
  have hcoord := hwithin hx
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hL' : 0 < N'.epsilon⁻¹ := inv_pos.mpr N'.epsilon_pos
  rcases hcapture with hright | hleft
  · by_cases haxis : (N.coordinate_inverse x).2 ≤ (3 / 4 : ℝ) * N.epsilon⁻¹
    · exact Or.inl ((mem_inner_slab_iff N).mpr ⟨hx.1, by linarith [hcoord.1.2.1], haxis⟩)
    · exact Or.inr (hright ⟨hx.1, by linarith, hcoord.1.2.2⟩)
  · by_cases haxis : -(3 / 4 : ℝ) * N'.epsilon⁻¹ ≤ (N'.coordinate_inverse x).2
    · exact Or.inr ((mem_inner_slab_iff N').mpr ⟨hx.2, haxis,
        by linarith [hcoord.2.2.2]⟩)
    · exact Or.inl (hleft ⟨hx.2, hcoord.2.2.1, by linarith⟩)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem mem_inner_slab_or_quarter (N : EpsilonNeck g) {x : M}
    (hx : x ∈ N.carrier) :
    x ∈ slab(N) ∨ x ∈ N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ∨
      x ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hcoord := (N.coordinate_inverse_mem x hx).2
  by_cases hlo : -(3 / 4 : ℝ) * N.epsilon⁻¹ ≤ (N.coordinate_inverse x).2
  · by_cases hhi : (N.coordinate_inverse x).2 ≤ (3 / 4 : ℝ) * N.epsilon⁻¹
    · exact Or.inl ((mem_inner_slab_iff N).mpr ⟨hx, hlo, hhi⟩)
    · exact Or.inr (Or.inr ⟨hx, by linarith, hcoord.2⟩)
  · exact Or.inr (Or.inl ⟨hx, hcoord.1, by linarith⟩)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in


theorem union_subset_inner_slabs_union_outer_quarters (N N' : EpsilonNeck g)
    (hpos : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier)
    (hneg : N'.region (-N'.epsilon⁻¹) (-N'.epsilon⁻¹ / 2) ⊆ N.carrier)
    (hwithin : N.carrier ∩ N'.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        N'.region (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2))
    (hcapture :
      N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ slab(N') ∨
      N'.region (-N'.epsilon⁻¹) (-N'.epsilon⁻¹ / 2) ⊆ slab(N)) :
    N.carrier ∪ N'.carrier ⊆ (slab(N) ∪ slab(N')) ∪
      (N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ∪
        N'.region (N'.epsilon⁻¹ / 2) N'.epsilon⁻¹) := by
  intro x hx
  have hoverlap := N.overlap_subset_inner_slabs_of_quarter_capture N' hwithin hcapture
  rcases hx with hx | hx
  · rcases mem_inner_slab_or_quarter N hx with hcore | hnegative | hpositive
    · exact Or.inl (Or.inl hcore)
    · exact Or.inr (Or.inl hnegative)
    · exact Or.inl (hoverlap ⟨hx, hpos hpositive⟩)
  · rcases mem_inner_slab_or_quarter N' hx with hcore | hnegative | hpositive
    · exact Or.inl (Or.inr hcore)
    · exact Or.inl (hoverlap ⟨hneg hnegative, hx⟩)
    · exact Or.inr (Or.inr hpositive)

end EpsilonNeck

namespace BalancedNeckChain

variable {ε : ℝ} (C : BalancedNeckChain g ε)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in


theorem mem_inner_slab_or_missing_neighbor_quarter
    (hcapture : ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      (C.neck i).region (ε⁻¹ / 2) ε⁻¹ ⊆ slab(C.neck (i + 1)) ∨
      (C.neck (i + 1)).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ slab(C.neck i))
    {i : ℤ} (hi : i ∈ C.shape.active) {x : M} (hx : x ∈ (C.neck i).carrier) :
    (∃ j ∈ C.shape.active, x ∈ slab(C.neck j)) ∨
      (i - 1 ∉ C.shape.active ∧ x ∈ (C.neck i).region (-ε⁻¹) (-ε⁻¹ / 2)) ∨
      (i + 1 ∉ C.shape.active ∧ x ∈ (C.neck i).region (ε⁻¹ / 2) ε⁻¹) := by
  have hoverlap (j : ℤ) (hj : j ∈ C.shape.active) (hj' : j + 1 ∈ C.shape.active) :
      (C.neck j).carrier ∩ (C.neck (j + 1)).carrier ⊆
        slab(C.neck j) ∪ slab(C.neck (j + 1)) := by
    apply (C.neck j).overlap_subset_inner_slabs_of_quarter_capture (C.neck (j + 1))
    · simpa only [C.epsilon_eq j hj, C.epsilon_eq (j + 1) hj'] using
        C.overlap_within_three_quarters j hj hj'
    · simpa only [C.epsilon_eq j hj, C.epsilon_eq (j + 1) hj'] using hcapture j hj hj'
  have hcases := EpsilonNeck.mem_inner_slab_or_quarter (C.neck i) hx
  rw [C.epsilon_eq i hi] at hcases
  rcases hcases with hcore | hnegative | hpositive
  · exact Or.inl ⟨i, hi, by simpa only [C.epsilon_eq i hi] using hcore⟩
  · by_cases hprev : i - 1 ∈ C.shape.active
    · have hi' : i - 1 + 1 ∈ C.shape.active := by simpa using hi
      have hneg := (C.overlap_contains_quarters (i - 1) hprev hi').2
      have hover := hoverlap (i - 1) hprev hi'
      simp only [sub_add_cancel] at hneg hover
      rcases hover ⟨hneg hnegative, hx⟩ with h | h
      · exact Or.inl ⟨i - 1, hprev, h⟩
      · exact Or.inl ⟨i, hi, h⟩
    · exact Or.inr (Or.inl ⟨hprev, hnegative⟩)
  · by_cases hnext : i + 1 ∈ C.shape.active
    · have hpos := (C.overlap_contains_quarters i hi hnext).1
      rcases hoverlap i hi hnext ⟨hx, hpos hpositive⟩ with h | h
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inl ⟨i + 1, hnext, h⟩
    · exact Or.inr (Or.inr ⟨hnext, hpositive⟩)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in


theorem carrier_subset_iUnion_inner_slabs_of_neighbors
    (hcapture : ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      (C.neck i).region (ε⁻¹ / 2) ε⁻¹ ⊆ slab(C.neck (i + 1)) ∨
      (C.neck (i + 1)).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ slab(C.neck i))
    {i : ℤ} (hi : i ∈ C.shape.active)
    (hprev : i - 1 ∈ C.shape.active) (hnext : i + 1 ∈ C.shape.active) :
    (C.neck i).carrier ⊆ ⋃ j : {j // j ∈ C.shape.active}, slab(C.neck j.1) := by
  intro x hx
  rcases C.mem_inner_slab_or_missing_neighbor_quarter hcapture hi hx with
    ⟨j, hj, hxj⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
  · exact (h hprev).elim
  · exact (h hnext).elim

end BalancedNeckChain

end PoincareConjecture
