import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Homotopy.HomotopyGroup








set_option autoImplicit false

open scoped Topology

namespace Poincare.Topology


theorem exists_stdSimplex_cube_coordinates (n : Nat) :
    Exists fun q : C((Fin n -> unitInterval), stdSimplex Real (Fin (n + 1))) =>
      And (forall t, q t 0 = ∏ k : Fin n, (1 - (t k : Real)))
        (forall t (j : Fin n), q t j.succ =
          (t j : Real) * ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1) := by
  let a (t : Fin n → unitInterval) : Fin (n + 1) → Real :=
    Fin.cases (∏ k : Fin n, (1 - (t k : Real)))
      (fun j => (t j : Real) * ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1)
  have ha (t : Fin n → unitInterval) : a t ∈ stdSimplex Real (Fin (n + 1)) := by
    constructor
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · change 0 ≤ ∏ k : Fin n, (1 - (t k : Real))
        exact Finset.prod_nonneg (fun k _ => sub_nonneg.mpr (t k).property.2)
      · apply mul_nonneg (t k).property.1
        apply Finset.prod_nonneg
        intro l _
        split_ifs
        · exact sub_nonneg.mpr (t l).property.2
        · exact zero_le_one
    · have hs := Finset.prod_one_sub_ordered (Finset.univ : Finset (OrderDual (Fin n)))
        (fun k => (t k : Real))
      simp only [Finset.prod_filter] at hs
      change (∏ k : Fin n, (1 - (t k : Real))) =
        1 - ∑ j : Fin n, (t j : Real) *
          ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1 at hs
      rw [Fin.sum_univ_succ]
      change (∏ k : Fin n, (1 - (t k : Real))) +
        (∑ j : Fin n, (t j : Real) *
          ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1) = 1
      rw [hs, sub_add_cancel]
  have hc : Continuous a := by
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · change Continuous (fun t : Fin n → unitInterval => ∏ k : Fin n, (1 - (t k : Real)))
      exact continuous_finsetProd _ (fun k _ =>
        continuous_const.sub (continuous_subtype_val.comp (continuous_apply k)))
    · apply (continuous_subtype_val.comp (continuous_apply k)).mul
      apply continuous_finsetProd
      intro l _
      by_cases hkl : k < l
      · simp only [if_pos hkl]
        exact continuous_const.sub (continuous_subtype_val.comp (continuous_apply l))
      · simp only [if_neg hkl]
        exact continuous_const
  exact ⟨⟨fun t => ⟨a t, ha t⟩, hc.subtype_mk ha⟩, fun _ => rfl, fun _ _ => rfl⟩


theorem stdSimplex_cube_coordinates_boundary_iff (n : Nat)
    (q : C((Fin n -> unitInterval), stdSimplex Real (Fin (n + 1))))
    (hq0 : forall t, q t 0 = ∏ k : Fin n, (1 - (t k : Real)))
    (hqs : forall t (j : Fin n), q t j.succ =
      (t j : Real) * ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1)
    (t : Fin n -> unitInterval) :
    (Exists fun j : Fin (n + 1) => q t j = 0) <-> t ∈ Cube.boundary (Fin n) := by
  constructor
  · rintro ⟨j, hj⟩
    cases j using Fin.cases with
    | zero =>
      rw [hq0] at hj
      obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp hj
      exact ⟨k, Or.inr (Subtype.ext (sub_eq_zero.mp hk).symm)⟩
    | succ j =>
      rw [hqs] at hj
      rcases mul_eq_zero.mp hj with hj | hj
      · exact ⟨j, Or.inl (Subtype.ext hj)⟩
      · obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp hj
        by_cases hjk : j < k
        · rw [if_pos hjk] at hk
          exact ⟨k, Or.inr (Subtype.ext (sub_eq_zero.mp hk).symm)⟩
        · rw [if_neg hjk] at hk
          exact False.elim (one_ne_zero hk)
  · rintro ⟨k, hk | hk⟩
    · refine ⟨k.succ, ?_⟩
      rw [hqs, hk]
      exact zero_mul _
    · refine ⟨0, ?_⟩
      rw [hq0]
      apply Finset.prod_eq_zero_iff.mpr
      refine ⟨k, Finset.mem_univ _, ?_⟩
      rw [hk]
      exact sub_self 1


theorem stdSimplex_cube_coordinates_injOn (n : Nat)
    (q : C((Fin n -> unitInterval), stdSimplex Real (Fin (n + 1))))
    (hqs : forall t (j : Fin n), q t j.succ =
      (t j : Real) * ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1) :
    Set.InjOn q (Set.compl (Cube.boundary (Fin n))) := by
  classical
  intro t ht u _ htu
  by_contra hne
  let s := Finset.univ.filter (fun k : Fin n => t k ≠ u k)
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  let j := s.max' hs
  have hj : t j ≠ u j := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have htail (k : Fin n) (hjk : j < k) : t k = u k := by
    by_contra hk
    have hks : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    exact (not_le_of_gt hjk) (s.le_max' k hks)
  have hp : (∏ k : Fin n, if j < k then 1 - (t k : Real) else 1) =
      ∏ k : Fin n, if j < k then 1 - (u k : Real) else 1 := by
    apply Finset.prod_congr rfl
    intro k _
    by_cases hjk : j < k
    · rw [if_pos hjk, if_pos hjk, htail k hjk]
    · rw [if_neg hjk, if_neg hjk]
  have hpos : 0 < ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1 := by
    apply Finset.prod_pos
    intro k _
    by_cases hjk : j < k
    · rw [if_pos hjk]
      apply sub_pos.mpr
      apply lt_of_le_of_ne (t k).property.2
      intro hk
      exact ht ⟨k, Or.inr (Subtype.ext hk)⟩
    · rw [if_neg hjk]
      exact zero_lt_one
  have heq := DFunLike.congr_fun htu j.succ
  rw [hqs, hqs, ← hp] at heq
  exact hj (Subtype.ext (mul_right_cancel₀ (ne_of_gt hpos) heq))


theorem stdSimplex_cube_coordinates_surjective (n : Nat)
    (q : C((Fin n -> unitInterval), stdSimplex Real (Fin (n + 1))))
    (hq0 : forall t, q t 0 = ∏ k : Fin n, (1 - (t k : Real)))
    (hqs : forall t (j : Fin n), q t j.succ =
      (t j : Real) * ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1) :
    Function.Surjective q := by
  induction n with
  | zero =>
    intro y
    refine ⟨fun j => j.elim0, Subtype.ext ?_⟩
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    change q (fun j => j.elim0) 0 = y 0
    rw [hq0]
    simp
  | succ n ih =>
    intro y
    let d : Real := y 0 + y 1
    let z : stdSimplex Real (Fin (n + 1)) :=
      ⟨Fin.cases d (fun j => y j.succ.succ), by
        constructor
        · intro j
          refine Fin.cases (add_nonneg (y.property.1 0) (y.property.1 1))
            (fun k => y.property.1 k.succ.succ) j
        · have hy := y.property.2
          rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hy
          rw [Fin.sum_univ_succ]
          change (y 0 + y 1) + (∑ j : Fin n, y j.succ.succ) = 1
          exact (add_assoc _ _ _).trans hy⟩
    obtain ⟨p, hp0, hps⟩ := exists_stdSimplex_cube_coordinates n
    obtain ⟨u, hu⟩ := ih p hp0 hps z
    have hu0 : (∏ k : Fin n, (1 - (u k : Real))) = d :=
      (hp0 u).symm.trans (DFunLike.congr_fun hu 0)
    have hus (j : Fin n) :
        (u j : Real) * (∏ k : Fin n, if j < k then 1 - (u k : Real) else 1) =
          y j.succ.succ :=
      (hps u j).symm.trans (DFunLike.congr_fun hu j.succ)
    obtain ⟨a, ha0, ha1⟩ : ∃ a : unitInterval,
        (1 - (a : Real)) * d = y 0 ∧ (a : Real) * d = y 1 := by
      by_cases hd : d = 0
      · have hz := (add_eq_zero_iff_of_nonneg (y.property.1 0) (y.property.1 1)).mp hd
        refine ⟨0, ?_, ?_⟩
        · change (1 - 0) * d = y 0
          rw [hd, mul_zero]
          exact hz.1.symm
        · change 0 * d = y 1
          rw [zero_mul]
          exact hz.2.symm
      · have hdpos : 0 < d :=
          lt_of_le_of_ne (add_nonneg (y.property.1 0) (y.property.1 1)) (Ne.symm hd)
        have hle : y 1 ≤ d := le_add_of_nonneg_left (y.property.1 0)
        let a : unitInterval :=
          ⟨y 1 / d, div_nonneg (y.property.1 1) hdpos.le, (div_le_one hdpos).mpr hle⟩
        have ha : (a : Real) * d = y 1 := div_mul_cancel₀ _ hd
        refine ⟨a, ?_, ha⟩
        rw [sub_mul, one_mul, ha]
        exact add_sub_cancel_right _ _
    refine ⟨Fin.cons a u, ?_⟩
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j
    · change q (Fin.cons a u) 0 = y 0
      rw [hq0, Fin.prod_univ_succ]
      change (1 - (a : Real)) * (∏ k : Fin n, (1 - (u k : Real))) = y 0
      rw [hu0]
      exact ha0
    · change q (Fin.cons a u) (0 : Fin (n + 1)).succ = y 1
      rw [hqs, Fin.prod_univ_succ]
      change (a : Real) * ((if (0 : Fin (n + 1)) < 0 then 1 - (a : Real) else 1) *
        ∏ k : Fin n, if 0 < k.succ then 1 - (u k : Real) else 1) = y 1
      rw [if_neg (lt_irrefl _), one_mul]
      have hp : (∏ k : Fin n, if 0 < k.succ then 1 - (u k : Real) else 1) =
          ∏ k : Fin n, (1 - (u k : Real)) := by
        apply Finset.prod_congr rfl
        intro k _
        exact if_pos k.succ_pos
      rw [hp, hu0]
      exact ha1
    · change q (Fin.cons a u) l.succ.succ = y l.succ.succ
      rw [hqs, Fin.prod_univ_succ]
      change (u l : Real) * ((if l.succ < 0 then 1 - (a : Real) else 1) *
        ∏ k : Fin n, if l.succ < k.succ then 1 - (u k : Real) else 1) = y l.succ.succ
      rw [if_neg (Fin.not_lt_zero _), one_mul]
      have hp : (∏ k : Fin n, if l.succ < k.succ then 1 - (u k : Real) else 1) =
          ∏ k : Fin n, if l < k then 1 - (u k : Real) else 1 := by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hlk : l < k
        · rw [if_pos (Fin.succ_lt_succ_iff.mpr hlk), if_pos hlk]
        · rw [if_neg (fun h => hlk (Fin.succ_lt_succ_iff.mp h)), if_neg hlk]
      rw [hp]
      exact hus l

end Poincare.Topology
