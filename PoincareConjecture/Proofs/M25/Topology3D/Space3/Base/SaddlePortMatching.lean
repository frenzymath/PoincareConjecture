import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HyperbolaDiscArcs
import Mathlib.Tactic









set_option autoImplicit false

open Set Function
open scoped Matrix

namespace PoincareConjecture.M25.Topology3D.SaddleOrientation



theorem port_sign_product_neg_of_scaled
    (a b sx0 sy0 sx1 sy1 : ℝ)
    (h : ((sx0 * a) * (sy0 * b)) *
      ((sx1 * a) * (sy1 * b)) < 0) :
    (sx0 * sy0) * (sx1 * sy1) < 0 := by
  by_contra hn
  have heq : ((sx0 * a) * (sy0 * b)) *
      ((sx1 * a) * (sy1 * b)) =
      ((sx0 * sy0) * (sx1 * sy1)) * (a * b) ^ 2 := by ring
  have hnonneg := mul_nonneg (le_of_not_gt hn) (sq_nonneg (a * b))
  rw [← heq] at hnonneg
  exact (not_lt_of_ge hnonneg) h



theorem exists_upper_arc_matching
    (ends : Fin 2 × Fin 2 ≃ Fin 4) :
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let other : Fin 2 → Fin 2 := ![1, 0]
    (∀ k : Fin 2,
      (ep.symm (ends (k, 0))).1 ≠ (ep.symm (ends (k, 1))).1) →
    (∀ k : Fin 2,
      (sx (ends (k, 0)) * sy (ends (k, 0))) *
        (sx (ends (k, 1)) * sy (ends (k, 1))) < 0) →
    ∃ label : Fin 2 ≃ Fin 2, ∀ k : Fin 2,
      ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) =
        {ep (label k, 0), ep (other (label k), 1)} := by
  classical
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let other : Fin 2 → Fin 2 := ![1, 0]
  change (∀ k : Fin 2,
      (ep.symm (ends (k, 0))).1 ≠ (ep.symm (ends (k, 1))).1) →
    (∀ k : Fin 2,
      (sx (ends (k, 0)) * sy (ends (k, 0))) *
        (sx (ends (k, 1)) * sy (ends (k, 1))) < 0) →
    ∃ label : Fin 2 ≃ Fin 2, ∀ k : Fin 2,
      ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) =
        {ep (label k, 0), ep (other (label k), 1)}
  intro hparent hsign
  let upperParent : Fin 4 → Fin 2 := ![0, 1, 1, 0]
  have htable (p q : Fin 4)
      (hl : (ep.symm p).1 ≠ (ep.symm q).1)
      (hs : (sx p * sy p) * (sx q * sy q) < 0) :
      upperParent p = upperParent q := by
    fin_cases p <;> fin_cases q <;>
      first
      | rfl
      | exact (hl (by decide)).elim
      | norm_num [sx, sy] at hs
  have hpair (p q : Fin 4) (hne : p ≠ q)
      (hsame : upperParent p = upperParent q) :
      ({p, q} : Set (Fin 4)) =
        {ep (upperParent p, 0), ep (other (upperParent p), 1)} := by
    fin_cases p <;> fin_cases q <;>
      simp_all [ep, finProdFinEquiv, other, upperParent, Set.pair_comm]
  have hends_ne (k : Fin 2) : ends (k, 0) ≠ ends (k, 1) := by
    intro h
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.snd (ends.injective h)
    exact zero_ne_one h01
  let label : Fin 2 → Fin 2 := fun k => upperParent (ends (k, 0))
  have hpairs (k : Fin 2) :
      ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) =
        {ep (label k, 0), ep (other (label k), 1)} :=
    hpair _ _ (hends_ne k) (htable _ _ (hparent k) (hsign k))
  have hlabel : Function.Injective label := by
    intro k l hkl
    have hsets : ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) =
        {ends (l, 0), ends (l, 1)} := by
      rw [hpairs k, hpairs l, hkl]
    have hx : ends (k, 0) ∈ ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) :=
      by simp
    rw [hsets] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · exact congrArg Prod.fst (ends.injective hx)
    · exact congrArg Prod.fst (ends.injective hx)
  let e : Fin 2 ≃ Fin 2 := Equiv.ofBijective label
    ⟨hlabel, Finite.surjective_of_injective hlabel⟩
  exact ⟨e, hpairs⟩

end PoincareConjecture.M25.Topology3D.SaddleOrientation
