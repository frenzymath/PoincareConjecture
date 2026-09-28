import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.Ring









set_option autoImplicit false

open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M02.Topology


theorem exists_stdSimplex_horn_retraction (n : Nat) (i : Fin (n + 2)) :
    ∃ r : C(stdSimplex Real (Fin (n + 2)),
      {p : stdSimplex Real (Fin (n + 2)) // ∃ j : Fin (n + 2), j ≠ i ∧ p j = 0}),
      ∀ y : {p : stdSimplex Real (Fin (n + 2)) //
        ∃ j : Fin (n + 2), j ≠ i ∧ p j = 0}, r y.val = y := by
  classical
  let S := stdSimplex Real (Fin (n + 2))
  let m (z : S) : Real :=
    Finset.univ.inf' Finset.univ_nonempty (fun k : Fin (n + 1) => z (i.succAbove k))
  have hm0 (z : S) : 0 ≤ m z :=
    Finset.le_inf' Finset.univ_nonempty _ (fun k _ => z.property.1 _)
  have hmle (z : S) (j : Fin (n + 2)) (hji : j ≠ i) : m z ≤ z j := by
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    exact Finset.inf'_le _ (Finset.mem_univ k)
  have hmcont : Continuous m :=
    Continuous.finset_inf'_apply Finset.univ_nonempty
      (fun k _ => (continuous_apply (i.succAbove k)).comp continuous_subtype_val)
  let f (z : S) (j : Fin (n + 2)) : Real :=
    if j = i then z i + ((n + 1 : Nat) : Real) * m z else z j - m z
  have hsum (z : S) : Finset.univ.sum (f z) = 1 := by
    rw [Fin.sum_univ_succAbove (f z) i]
    have hfi : f z i = z i + ((n + 1 : Nat) : Real) * m z := if_pos rfl
    have hfaces :
        Finset.univ.sum (fun k : Fin (n + 1) => f z (i.succAbove k)) =
          Finset.univ.sum (fun k : Fin (n + 1) => z (i.succAbove k) - m z) := by
      apply Finset.sum_congr rfl
      intro k _
      exact if_neg (Fin.succAbove_ne i k)
    rw [hfi, hfaces, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hz : Finset.univ.sum (fun j : Fin (n + 2) => z j) = 1 := z.property.2
    rw [Fin.sum_univ_succAbove (fun j => z j) i] at hz
    convert hz using 1
    ring
  have hmem (z : S) : f z ∈ stdSimplex Real (Fin (n + 2)) := by
    refine ⟨?_, hsum z⟩
    intro j
    by_cases hji : j = i
    · simp only [f, if_pos hji]
      exact add_nonneg (z.property.1 i) (mul_nonneg (Nat.cast_nonneg _) (hm0 z))
    · simp only [f, if_neg hji]
      exact sub_nonneg.mpr (hmle z j hji)
  have hhorn (z : S) : ∃ j : Fin (n + 2), j ≠ i ∧ f z j = 0 := by
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun k : Fin (n + 1) => z (i.succAbove k))
    refine ⟨i.succAbove k, Fin.succAbove_ne _ _, ?_⟩
    change (if i.succAbove k = i then _ else _) = 0
    rw [if_neg (Fin.succAbove_ne _ _)]
    exact sub_eq_zero.mpr hk.symm
  have hfcont : Continuous f := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · simp only [f, if_pos hji]
      exact ((continuous_apply i).comp continuous_subtype_val).add
        (continuous_const.mul hmcont)
    · simp only [f, if_neg hji]
      exact ((continuous_apply j).comp continuous_subtype_val).sub hmcont
  let r : C(S, {p : S // ∃ j : Fin (n + 2), j ≠ i ∧ p j = 0}) :=
    ⟨fun z => ⟨⟨f z, hmem z⟩, hhorn z⟩,
      (hfcont.subtype_mk hmem).subtype_mk hhorn⟩
  refine ⟨r, ?_⟩
  intro y
  obtain ⟨j, hji, hj⟩ := y.property
  have hmy : m y.val = 0 := by
    have h := hmle y.val j hji
    rw [hj] at h
    exact le_antisymm h (hm0 y.val)
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change f y.val k = y.val k
  by_cases hki : k = i
  · subst k
    simp only [f, if_pos rfl, hmy, mul_zero, add_zero]
  · simp only [f, if_neg hki, hmy, sub_zero]


theorem exists_stdSimplex_horn_extension
    {X : Type u} [TopologicalSpace X] (n : Nat) (i : Fin (n + 2))
    (g : C({p : stdSimplex Real (Fin (n + 2)) //
      ∃ j : Fin (n + 2), j ≠ i ∧ p j = 0}, X)) :
    ∃ f : C(stdSimplex Real (Fin (n + 2)), X),
      ∀ y : {p : stdSimplex Real (Fin (n + 2)) //
        ∃ j : Fin (n + 2), j ≠ i ∧ p j = 0}, f y.val = g y := by
  obtain ⟨r, hr⟩ := exists_stdSimplex_horn_retraction n i
  refine ⟨g.comp r, ?_⟩
  intro y
  change g (r y.val) = g y
  rw [hr y]

end PoincareConjecture.Proofs.M02.Topology
