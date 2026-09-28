import PoincareConjecture.Proofs.M02.Topology.FiniteOrderComplexPivots

set_option autoImplicit false

open scoped BigOperators

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

theorem sum_abs_le_of_coordinate_pivots
    {I : Type u} {V : Type v} [Fintype V]
    (c : I → V → Real) (eta : Real) (heta : 0 < eta)
    (t : Finset I) (hc : ∀ i ∈ t, ‖c i‖ ≤ 1)
    (hpivot : ∀ (s : Finset I), s ⊆ t → s.Nonempty →
      ∃ i ∈ s, ∃ v : V, eta ≤ |c i v| ∧
        ∀ j ∈ s, j ≠ i → c j v = 0)
    (w : I → Real) :
    ∑ i ∈ t, |w i| ≤ ((1 + eta⁻¹) ^ t.card - 1) * ‖∑ i ∈ t, w i • c i‖ := by
  classical
  induction t using Finset.strongInductionOn with
  | _ t ih =>
    by_cases ht : t.Nonempty
    · obtain ⟨i, hi, v, hvi, hother⟩ := hpivot t (Finset.Subset.refl t) ht
      let z : V → Real := ∑ j ∈ t, w j • c j
      have hzv : z v = w i * c i v := by
        change (∑ j ∈ t, w j • c j) v = _
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_single i
        · intro j hj hji
          rw [hother j hj hji, mul_zero]
        · exact fun h => (h hi).elim
      have hwi : |w i| ≤ eta⁻¹ * ‖z‖ := by
        have hmul : |w i| * eta ≤ ‖z‖ := calc
          |w i| * eta ≤ |w i| * |c i v| :=
            mul_le_mul_of_nonneg_left hvi (abs_nonneg _)
          _ = |z v| := by rw [hzv, abs_mul]
          _ ≤ ‖z‖ := norm_le_pi_norm z v
        calc
          |w i| ≤ ‖z‖ / eta := (le_div_iff₀ heta).mpr hmul
          _ = eta⁻¹ * ‖z‖ := by ring
      have hdecomp : z = w i • c i + ∑ j ∈ t.erase i, w j • c j := by
        exact (Finset.add_sum_erase _ _ hi).symm
      have hrest : ‖∑ j ∈ t.erase i, w j • c j‖ ≤ (1 + eta⁻¹) * ‖z‖ := by
        have heq : ∑ j ∈ t.erase i, w j • c j = z - w i • c i := by
          rw [hdecomp]
          abel
        rw [heq]
        calc
          ‖z - w i • c i‖ ≤ ‖z‖ + ‖w i • c i‖ := norm_sub_le _ _
          _ = ‖z‖ + |w i| * ‖c i‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ ‖z‖ + |w i| := by
            exact add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg (w i)) (hc i hi))
          _ ≤ (1 + eta⁻¹) * ‖z‖ := by nlinarith
      have hind := ih (t.erase i) (Finset.erase_ssubset hi)
        (fun j hj => hc j (Finset.mem_of_mem_erase hj))
        (fun s hs hsne => hpivot s (hs.trans (Finset.erase_subset _ _)) hsne)
      have hbase : 1 ≤ 1 + eta⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr heta.le)
      have hcoef : 0 ≤ (1 + eta⁻¹) ^ (t.erase i).card - 1 := by
        exact sub_nonneg.mpr (one_le_pow₀ hbase)
      have hcard : (t.erase i).card + 1 = t.card := Finset.card_erase_add_one hi
      calc
        ∑ j ∈ t, |w j| = |w i| + ∑ j ∈ t.erase i, |w j| :=
          (Finset.add_sum_erase _ _ hi).symm
        _ ≤ eta⁻¹ * ‖z‖ +
            ((1 + eta⁻¹) ^ (t.erase i).card - 1) *
              ((1 + eta⁻¹) * ‖z‖) :=
          add_le_add hwi (hind.trans (mul_le_mul_of_nonneg_left hrest hcoef))
        _ = ((1 + eta⁻¹) ^ t.card - 1) * ‖z‖ := by
          rw [← hcard, pow_succ]
          ring
    · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      simp only [ht0, Finset.sum_empty, Finset.card_empty, pow_zero, sub_self,
        norm_zero, mul_zero, le_refl]

theorem sum_abs_le_of_strict_supports
    {I : Type u} [PartialOrder I] {V : Type v} [Fintype V]
    (c : I → V → Real) (support : I → Finset V)
    (hc : ∀ i v, c i v ≠ 0 ↔ v ∈ support i)
    (hsupport : ∀ i, (support i).Nonempty)
    (hstrict : ∀ {i j : I}, i < j → support i ⊂ support j)
    (eta : Real) (heta : 0 < eta)
    (hgap : ∀ i v, v ∈ support i → eta ≤ |c i v|)
    (hnorm : ∀ i, ‖c i‖ ≤ 1)
    (t : Finset I) (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i)
    (w : I → Real) :
    ∑ i ∈ t, |w i| ≤ ((1 + eta⁻¹) ^ t.card - 1) * ‖∑ i ∈ t, w i • c i‖ := by
  apply sum_abs_le_of_coordinate_pivots c eta heta t (fun i _ => hnorm i) _ w
  intro s hst hs
  obtain ⟨i, hi, v, hv, hnot⟩ := exists_chain_coordinate_pivot_of_strict_supports
    support hsupport hstrict s hs (fun i hi j hj => hchain i (hst hi) j (hst hj))
  refine ⟨i, hi, v, hgap i v hv, ?_⟩
  intro j hj hji
  exact not_ne_iff.mp ((hc j v).not.mpr (hnot j hj hji))

end PoincareConjecture.Proofs.M02.Topology
