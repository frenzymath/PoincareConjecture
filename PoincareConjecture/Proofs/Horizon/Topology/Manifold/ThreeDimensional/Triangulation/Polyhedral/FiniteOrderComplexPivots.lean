import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Polyhedral.FiniteOrderComplex
import Mathlib.Order.Preorder.Finite









set_option autoImplicit false

open scoped BigOperators

universe u v

namespace Poincare.Topology

theorem affineIndependent_of_chain_coordinate_pivots
    {I : Type u} [PartialOrder I]
    {V : Type v} (c : I → V → Real)
    (hpivot : ∀ (t : Finset I), t.Nonempty →
      (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) →
      ∃ i ∈ t, ∃ v : V,
        (∀ j ∈ t, j ≠ i → c j v = 0) ∧ c i v ≠ 0)
    (t : Finset I)
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) :
    AffineIndependent Real (fun i : t => c i) := by
  classical
  apply LinearIndependent.affineIndependent
  rw [linearIndependent_iff']
  intro s w hsum i hi
  by_contra hwi
  let u : Finset t := s.filter (fun j => w j ≠ 0)
  have hu : u.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hwi⟩⟩
  let vset : Finset I := u.image Subtype.val
  have hvchain : ∀ i ∈ vset, ∀ j ∈ vset, i ≤ j ∨ j ≤ i := by
    intro j hj k hk
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hk
    exact hchain j' j'.property k' k'.property
  obtain ⟨j, hj, v, hrest, hcj⟩ := hpivot vset (hu.image Subtype.val) hvchain
  obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
  have hjw : w j' ≠ 0 := (Finset.mem_filter.mp hj').2
  have heval : ∑ k ∈ s, w k * c k v = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrArg (fun q : V → Real => q v) hsum
  have hcollapse : ∑ k ∈ s, w k * c k v = w j' * c j' v := by
    apply Finset.sum_eq_single j'
    · intro k hk hkj
      by_cases hwk : w k = 0
      · simp only [hwk, zero_mul]
      · have hkv : k.val ∈ vset := Finset.mem_image.mpr
          ⟨k, Finset.mem_filter.mpr ⟨hk, hwk⟩, rfl⟩
        have hne : k.val ≠ j'.val := fun h => hkj (Subtype.ext h)
        rw [hrest k hkv hne, mul_zero]
    · intro hjnot
      exact (hjnot (Finset.mem_filter.mp hj').1).elim
  rw [hcollapse] at heval
  exact (mul_ne_zero hjw hcj) heval

theorem chain_weighted_coordinates_unique
    {I : Type u} [PartialOrder I]
    {V : Type v} (c : I → V → Real)
    (hpivot : ∀ (t : Finset I), t.Nonempty →
      (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) →
      ∃ i ∈ t, ∃ v : V,
        (∀ j ∈ t, j ≠ i → c j v = 0) ∧ c i v ≠ 0)
    (t : Finset I)
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i)
    (z z' : t → Real) (hz : ∑ i, z i = 1) (hz' : ∑ i, z' i = 1)
    (heq : ∑ i, z i • c i = ∑ i, z' i • c i) :
    ∀ i, z i = z' i := by
  have hi := affineIndependent_of_chain_coordinate_pivots c hpivot t hchain
  intro i
  apply hi.eq_of_sum_eq_sum (s := (Finset.univ : Finset t))
    (w₁ := z) (w₂ := z') ?_ ?_ i (Finset.mem_univ i)
  · simpa using hz.trans hz'.symm
  · simpa using heq

theorem affineIndependent_of_chain_support_pivots
    {I : Type u} [PartialOrder I]
    {V : Type v} (c : I → V → Real) (support : I → Finset V)
    (hc : ∀ i v, c i v ≠ 0 ↔ v ∈ support i)
    (hpivot : ∀ (t : Finset I), t.Nonempty →
      (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) →
      ∃ i ∈ t, ∃ v ∈ support i,
        ∀ j ∈ t, j ≠ i → v ∉ support j)
    (t : Finset I)
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) :
    AffineIndependent Real (fun i : t => c i) := by
  apply affineIndependent_of_chain_coordinate_pivots c
  · intro u hu huc
    obtain ⟨i, hi, v, hvi, hnot⟩ := hpivot u hu huc
    refine ⟨i, hi, v, ?_, (hc i v).2 hvi⟩
    intro j hj hji
    exact not_ne_iff.mp ((hc j v).not.mpr (hnot j hj hji))
  · exact hchain

theorem exists_chain_coordinate_pivot_of_strict_supports
    {I : Type u} [PartialOrder I]
    {V : Type v} (support : I → Finset V)
    (hsupport : ∀ i, (support i).Nonempty)
    (hstrict : ∀ {i j : I}, i < j → support i ⊂ support j)
    (t : Finset I) (ht : t.Nonempty)
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) :
    ∃ i ∈ t, ∃ v ∈ support i,
      ∀ j ∈ t, j ≠ i → v ∉ support j := by
  classical
  obtain ⟨i, hi⟩ := Finset.exists_maximal ht
  have hi_mem : i ∈ t := hi.1
  by_cases hempty : t.erase i = ∅
  · obtain ⟨v, hv⟩ := hsupport i
    refine ⟨i, hi_mem, v, hv, ?_⟩
    intro j hj hji
    have hjempty : j ∉ t.erase i := by simp [hempty]
    exact (hjempty (Finset.mem_erase.mpr ⟨hji, hj⟩)).elim
  · have hneerase : (t.erase i).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨j, hj⟩ := Finset.exists_maximal hneerase
    have hj_mem : j ∈ t := Finset.mem_of_mem_erase hj.1
    have hji_le_or : j ≤ i ∨ i ≤ j := hchain j hj_mem i hi_mem
    have hji : j < i := by
      rcases hji_le_or with hle | hle
      · exact lt_of_le_of_ne hle (fun heq => (Finset.mem_erase.mp hj.1).1 heq)
      · have heq : i = j := hi.eq_of_le hj_mem hle
        exact ((Finset.mem_erase.mp hj.1).1 heq.symm).elim
    obtain ⟨hsub, hnsub⟩ := hstrict hji
    have hnot : ¬ support i ⊆ support j := by
      intro h
      exact hnsub h
    obtain ⟨v, hvi, hvj⟩ := Finset.not_subset.mp hnot
    refine ⟨i, hi_mem, v, hvi, ?_⟩
    intro k hk hki
    have hki_le : k ≤ i := by
      rcases hchain k hk i hi_mem with hle | hle
      · exact hle
      · exact (hi.eq_of_le hk hle).symm.le
    have hki_lt : k < i := lt_of_le_of_ne hki_le hki
    have hkj_or : k ≤ j ∨ j ≤ k := hchain k hk j hj_mem
    rcases hkj_or with hkj | hkj
    · intro hvk
      by_cases hkj' : k = j
      · exact hvj (hkj' ▸ hvk)
      · have hlt : k < j := lt_of_le_of_ne hkj hkj'
        obtain ⟨hsubkj, _⟩ := hstrict hlt
        exact hvj (hsubkj hvk)
    · have heq : j = k := hj.eq_of_le (Finset.mem_erase.mpr ⟨hki, hk⟩) hkj
      simpa [heq] using hvj

theorem affineIndependent_of_strict_supports
    {I : Type u} [PartialOrder I]
    {V : Type v} (c : I → V → Real) (support : I → Finset V)
    (hc : ∀ i v, c i v ≠ 0 ↔ v ∈ support i)
    (hsupport : ∀ i, (support i).Nonempty)
    (hstrict : ∀ {i j : I}, i < j → support i ⊂ support j)
    (t : Finset I)
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) :
    AffineIndependent Real (fun i : t => c i) := by
  apply affineIndependent_of_chain_support_pivots c support hc
    (fun u hu huc => exists_chain_coordinate_pivot_of_strict_supports
      support hsupport hstrict u hu huc) t hchain

theorem chain_representatives_injective_of_strict_supports
    {I : Type u} [PartialOrder I]
    {V : Type v} (c : I → V → Real) (support : I → Finset V)
    (hc : ∀ i v, c i v ≠ 0 ↔ v ∈ support i)
    (hsupport : ∀ i, (support i).Nonempty)
    (hstrict : ∀ {i j : I}, i < j → support i ⊂ support j)
    (t : Finset I)
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) :
    Set.InjOn c (t : Set I) := by
  have hi := affineIndependent_of_strict_supports c support hc hsupport hstrict t hchain
  intro i hi' j hj' heq
  have hij : (⟨i, hi'⟩ : t) = ⟨j, hj'⟩ :=
    hi.injective (show c ((⟨i, hi'⟩ : t) : I) = c ((⟨j, hj'⟩ : t) : I) from heq)
  exact congrArg Subtype.val hij

end Poincare.Topology
