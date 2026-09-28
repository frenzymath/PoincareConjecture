import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Flags.FiniteFlagDisplacement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Flags.FiniteFlagComparison








set_option autoImplicit false

open Set Metric
open scoped BigOperators

universe u v

namespace Poincare.Topology

open scoped Classical in
theorem geometric_flag_displacement_bound
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    {I : Type v} [PartialOrder I]
    (s : I → Finset E) (horder : ∀ i j, i ≤ j ↔ s i ⊆ s j)
    (hsne : ∀ i, (s i).Nonempty)
    (a : Real) (ha : 0 < a)
    (halt : ∀ i, ∀ v ∈ s i,
      a ≤ infDist v (affineSpan Real (((s i).erase v : Finset E) : Set E) : Set E))
    (c d : I → E) (eta : Real) (heta : 0 < eta)
    (hc : ∀ i, ∃ w : E → Real, (∀ v ∈ s i, eta ≤ w v) ∧
      (∑ v ∈ s i, w v) = 1 ∧ (∑ v ∈ s i, w v • v) = c i)
    (delta : Real) (hdelta : 0 ≤ delta) (hd : ∀ i, ‖d i - c i‖ ≤ delta)
    (t : Finset I) (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i)
    (w : I → Real) (hsumw : ∑ i ∈ t, w i = 0) :
    ‖∑ i ∈ t, w i • (d i - c i)‖ ≤
      (delta / a * ((1 + eta⁻¹) ^ t.card - 1)) * ‖∑ i ∈ t, w i • c i‖ := by
  classical
  by_cases ht : t.Nonempty
  swap
  · have ht0 := Finset.not_nonempty_iff_eq_empty.mp ht
    simp only [ht0, Finset.sum_empty, norm_zero, mul_zero, le_refl]
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_maximal ht
  have hsub (i : t) : s i.val ⊆ s j := by
    rcases hchain i i.property j hj with hij | hji
    · exact (horder i j).mp hij
    · exact (horder i j).mp (hjmax i.property hji)
  choose W hW hWsum hWval using hc
  let C (i : t) (v : s j) : Real := if (v : E) ∈ s i.val then W i.val v else 0
  let S (i : t) : Finset (s j) := Finset.univ.filter (fun v => (v : E) ∈ s i.val)
  have hCnonneg (i : t) (v : s j) : 0 ≤ C i v := by
    dsimp [C]
    split_ifs with hv
    · exact heta.le.trans (hW i v hv)
    · exact le_rfl
  have hC (i : t) (v : s j) : C i v ≠ 0 ↔ v ∈ S i := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : (v : E) ∈ s i.val
    · simp only [C, if_pos hv, hv, iff_true]
      exact ne_of_gt (heta.trans_le (hW i v hv))
    · simp only [C, if_neg hv, ne_eq, not_true_eq_false, hv]
  have hSne (i : t) : (S i).Nonempty := by
    obtain ⟨v, hv⟩ := hsne i
    exact ⟨⟨v, hsub i hv⟩, by simp only [S, Finset.mem_filter, Finset.mem_univ,
      true_and, hv]⟩
  have hSstrict {i k : t} (hik : i < k) : S i ⊂ S k := by
    have hisub : s i.val ⊆ s k.val := (horder i k).mp hik.le
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hisub (Finset.mem_filter.mp hv).2⟩
    · intro heq
      have hrev : s k.val ⊆ s i.val := by
        intro v hv
        let v' : s j := ⟨v, hsub k hv⟩
        have hmem : v' ∈ S k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        rw [← heq] at hmem
        exact (Finset.mem_filter.mp hmem).2
      exact (not_le_of_gt hik) ((horder k i).mpr hrev)
  have hCgap (i : t) (v : s j) (hv : v ∈ S i) : eta ≤ |C i v| := by
    have hv' := (Finset.mem_filter.mp hv).2
    rw [abs_of_nonneg (hCnonneg i v)]
    rw [show C i v = W i.val v from if_pos hv']
    exact hW i v hv'
  have hCsum (i : t) : ∑ v : s j, C i v = 1 := by
    calc
      (∑ v : s j, C i v) =
          ∑ v ∈ s j, if v ∈ s i.val then W i.val v else 0 :=
        Finset.sum_coe_sort (s j) (fun v : E => if v ∈ s i.val then W i.val v else 0)
      _ =
          ∑ v ∈ s i.val, if v ∈ s i.val then W i.val v else 0 :=
        (Finset.sum_subset (hsub i) (fun v _ hv => if_neg hv)).symm
      _ = ∑ v ∈ s i.val, W i.val v :=
        Finset.sum_congr rfl (fun v hv => if_pos hv)
      _ = 1 := hWsum i
  have hCval (i : t) : (∑ v : s j, C i v • (v : E)) = c i.val := by
    calc
      (∑ v : s j, C i v • (v : E)) =
          ∑ v ∈ s j, (if v ∈ s i.val then W i.val v else 0) • v :=
        Finset.sum_coe_sort (s j)
          (fun v : E => (if v ∈ s i.val then W i.val v else 0) • v)
      _ =
          ∑ v ∈ s i.val, (if v ∈ s i.val then W i.val v else 0) • v :=
        (Finset.sum_subset (hsub i) (fun v _ hv => by rw [if_neg hv, zero_smul])).symm
      _ = ∑ v ∈ s i.val, W i.val v • v :=
        Finset.sum_congr rfl (fun v hv => by rw [if_pos hv])
      _ = c i.val := hWval i
  have hCnorm (i : t) : ‖C i‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro v
    rw [Real.norm_eq_abs, abs_of_nonneg (hCnonneg i v)]
    calc
      C i v ≤ ∑ v' : s j, C i v' :=
        Finset.single_le_sum (fun v' _ => hCnonneg i v') (Finset.mem_univ v)
      _ = 1 := hCsum i
  have hsum : ∑ i : t, w i.val = 0 :=
    (Finset.sum_coe_sort t w).trans hsumw
  have hbound := finite_flag_displacement_bound (s j) a ha (halt j)
    C S hC hSne hSstrict eta heta hCgap hCnorm hCsum
    (fun i : t => d i.val - c i.val) delta hdelta Finset.univ
    (fun i _ k _ => hchain i i.property k k.property)
    (fun i _ => hd i) (fun i : t => w i.val) hsum
  simp only [hCval, Finset.card_univ, Fintype.card_coe] at hbound
  rw [Finset.sum_coe_sort t (fun i : I => w i • (d i - c i)),
    Finset.sum_coe_sort t (fun i : I => w i • c i)] at hbound
  exact hbound

open scoped Classical in
theorem geometric_flag_displacement_bound_of_card_le
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    {I : Type v} [PartialOrder I]
    (s : I → Finset E) (horder : ∀ i j, i ≤ j ↔ s i ⊆ s j)
    (hsne : ∀ i, (s i).Nonempty)
    (a : Real) (ha : 0 < a)
    (halt : ∀ i, ∀ v ∈ s i,
      a ≤ infDist v (affineSpan Real (((s i).erase v : Finset E) : Set E) : Set E))
    (c d : I → E) (eta : Real) (heta : 0 < eta)
    (hc : ∀ i, ∃ w : E → Real, (∀ v ∈ s i, eta ≤ w v) ∧
      (∑ v ∈ s i, w v) = 1 ∧ (∑ v ∈ s i, w v • v) = c i)
    (delta : Real) (hdelta : 0 ≤ delta) (hd : ∀ i, ‖d i - c i‖ ≤ delta)
    (m : Nat) (t : Finset I) (hcard : t.card ≤ m)
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i)
    (w : I → Real) (hsumw : ∑ i ∈ t, w i = 0) :
    ‖∑ i ∈ t, w i • (d i - c i)‖ ≤
      (delta / a * ((1 + eta⁻¹) ^ m - 1)) * ‖∑ i ∈ t, w i • c i‖ := by
  have h := geometric_flag_displacement_bound s horder hsne a ha halt c d eta heta
    hc delta hdelta hd t hchain w hsumw
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hdelta ha.le)
  exact sub_le_sub_right
    (pow_le_pow_right₀ (le_add_of_nonneg_right (inv_nonneg.mpr heta.le)) hcard) 1

open scoped Classical in
theorem geometricFlagComparison_displacement_lipschitzOn
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    {I : Type v} [PartialOrder I] [Fintype I]
    (s : I → Finset E) (horder : ∀ i j, i ≤ j ↔ s i ⊆ s j)
    (hsne : ∀ i, (s i).Nonempty)
    (a : Real) (ha : 0 < a)
    (halt : ∀ i, ∀ v ∈ s i,
      a ≤ infDist v (affineSpan Real (((s i).erase v : Finset E) : Set E) : Set E))
    (c d : I → E) (eta : Real) (heta : 0 < eta)
    (hc : ∀ i, ∃ w : E → Real, (∀ v ∈ s i, eta ≤ w v) ∧
      (∑ v ∈ s i, w v) = 1 ∧ (∑ v ∈ s i, w v • v) = c i)
    (delta : Real) (hdelta : 0 ≤ delta) (hd : ∀ i, ‖d i - c i‖ ≤ delta)
    (m : Nat) (hcard : ∀ t : Finset I,
      (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) → t.card ≤ m)
    (hinj : Function.Injective (finiteOrderComplexMap I c))
    (kappa : NNReal)
    (hkappa : delta / a * ((1 + eta⁻¹) ^ m - 1) ≤ (kappa : Real))
    (U : Set E) (hU : Convex Real U)
    (hUr : U ⊆ Set.range (finiteOrderComplexMap I c)) :
    LipschitzOnWith kappa (fun x => finiteFlagComparison c d hinj x - x) U := by
  apply finiteFlagComparison_displacement_lipschitzOn c d hinj kappa _ U hU hUr
  intro t hchain w hsum
  exact (geometric_flag_displacement_bound_of_card_le s horder hsne a ha halt
    c d eta heta hc delta hdelta hd m t (hcard t hchain) hchain w hsum).trans
      (mul_le_mul_of_nonneg_right hkappa (norm_nonneg _))

end Poincare.Topology
