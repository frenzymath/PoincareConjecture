import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

noncomputable section

open scoped BigOperators

universe u

namespace PoincareConjecture.Proofs.M02.Topology

def stdSimplexPrismSimplex (n : Nat) (i : Fin (n + 1)) :
    C(stdSimplex Real (Fin (n + 2)),
      stdSimplex Real (Fin (n + 1)) × unitInterval) := by
  let t (z : stdSimplex Real (Fin (n + 2))) : Real :=
    ∑ k : Fin (n + 2), if i.castSucc < k then z k else 0
  have ht (z : stdSimplex Real (Fin (n + 2))) : t z ∈ unitInterval := by
    constructor
    · apply Finset.sum_nonneg
      intro k _
      split_ifs
      · exact z.property.1 k
      · exact le_rfl
    · calc
        t z ≤ ∑ k : Fin (n + 2), z k := by
          apply Finset.sum_le_sum
          intro k _
          split_ifs
          · exact le_rfl
          · exact z.property.1 k
        _ = 1 := z.property.2
  have hc : Continuous t := by
    apply continuous_finsetSum
    intro k _
    by_cases hk : i.castSucc < k
    · simp only [if_pos hk]
      exact (continuous_apply k).comp continuous_subtype_val
    · simp only [if_neg hk]
      exact continuous_const
  exact ⟨fun z => (stdSimplex.map i.predAbove z, ⟨t z, ht z⟩),
    (stdSimplex.continuous_map i.predAbove).prodMk (hc.subtype_mk ht)⟩

def stdSimplexPrismSide (n : Nat) (j : Fin (n + 2)) :
    C(stdSimplex Real (Fin (n + 1)) × unitInterval,
      stdSimplex Real (Fin (n + 2)) × unitInterval) :=
  ⟨fun p => (stdSimplex.map j.succAbove p.1, p.2),
    ((stdSimplex.continuous_map j.succAbove).comp continuous_fst).prodMk continuous_snd⟩

def stdSimplexPrismEnd (n : Nat) (t : unitInterval) :
    C(stdSimplex Real (Fin (n + 1)),
      stdSimplex Real (Fin (n + 1)) × unitInterval) :=
  ⟨fun z => (z, t), continuous_id.prodMk continuous_const⟩

set_option maxHeartbeats 1000000 in

theorem exists_stdSimplex_prism_gluing
    {X : Type u} [TopologicalSpace X] (n : Nat)
    (f : Fin (n + 1) -> C(stdSimplex Real (Fin (n + 2)), X))
    (hf : forall (i j : Fin (n + 1))
      (z w : stdSimplex Real (Fin (n + 2))),
      stdSimplexPrismSimplex n i z = stdSimplexPrismSimplex n j w ->
        f i z = f j w) :
    Exists fun F : C(stdSimplex Real (Fin (n + 1)) × unitInterval, X) =>
      forall i, F.comp (stdSimplexPrismSimplex n i) = f i := by
  classical
  let D := Sigma (fun _ : Fin (n + 1) => stdSimplex Real (Fin (n + 2)))
  let Q : C(D, stdSimplex Real (Fin (n + 1)) × unitInterval) :=
    ⟨fun z => stdSimplexPrismSimplex n z.1 z.2,
      continuous_sigma (fun i => (stdSimplexPrismSimplex n i).continuous)⟩
  have hsurj : Function.Surjective Q := by
    rintro ⟨x, t⟩
    let S (i : Fin (n + 1)) : Real := ∑ k : Fin (n + 1), if i < k then x k else 0
    let U (i : Fin (n + 1)) : Real := ∑ k : Fin (n + 1), if i ≤ k then x k else 0
    have hSU (i : Fin (n + 1)) : U i = S i + x i := by
      dsimp only [S, U]
      rw [Fin.sum_univ_succAbove (fun k => if i ≤ k then x k else 0) i,
        Fin.sum_univ_succAbove (fun k => if i < k then x k else 0) i]
      simp only [le_rfl, if_true, lt_self_iff_false, if_false, zero_add]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      have hne : i.val ≠ (i.succAbove k).val :=
        fun h => Fin.succAbove_ne i k (Fin.ext h.symm)
      by_cases hik : i < i.succAbove k
      · rw [if_pos hik.le, if_pos hik]
      · have hle : ¬i ≤ i.succAbove k := by
          change ¬i.val ≤ (i.succAbove k).val
          change ¬i.val < (i.succAbove k).val at hik
          omega
        rw [if_neg hle, if_neg hik]
    have hlast : S (Fin.last n) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact if_neg (not_lt_of_ge (Fin.le_last k))
    have hfirst : U 0 = 1 := by
      change (∑ k : Fin (n + 1), if (0 : Fin (n + 1)) ≤ k then x k else 0) = 1
      simp only [Fin.zero_le, if_true]
      exact x.property.2
    have hnext (i : Fin n) : S i.castSucc = U i.succ := by
      apply Finset.sum_congr rfl
      intro k _
      have he : i.castSucc < k ↔ i.succ ≤ k := by
        change i.val < k.val ↔ i.val + 1 ≤ k.val
        omega
      simp only [he]
    have hcover : ∃ i : Fin (n + 1), S i ≤ (t : Real) ∧ (t : Real) ≤ U i := by
      by_contra h
      have above (i : Fin (n + 1)) : U i < (t : Real) := by
        induction i using Fin.reverseInduction with
        | last =>
          apply lt_of_not_ge
          intro hi
          exact h ⟨Fin.last n, hlast.symm ▸ t.property.1, hi⟩
        | cast i ih =>
          apply lt_of_not_ge
          intro hi
          exact h ⟨i.castSucc, (hnext i).trans_le ih.le, hi⟩
      exact (not_lt_of_ge t.property.2) (hfirst ▸ above 0)
    obtain ⟨i, hi0, hi1⟩ := hcover
    let lo : Real := S i + x i - (t : Real)
    let hi : Real := (t : Real) - S i
    have hlo : 0 ≤ lo := sub_nonneg.mpr ((hSU i) ▸ hi1)
    have hhi : 0 ≤ hi := sub_nonneg.mpr hi0
    have hsum : lo + hi = x i := by
      change (S i + x i - (t : Real)) + ((t : Real) - S i) = x i
      rw [sub_add_sub_cancel, add_sub_cancel_left]
    let w : Fin (n + 1) → Real := Function.update (fun k => x k) i hi
    let zval : Fin (n + 2) → Real :=
      Fin.insertNth (α := fun _ : Fin (n + 2) => Real) i.castSucc lo w
    have hwi : w i = hi := Function.update_self i hi (fun k => x k)
    have hw (j : Fin n) : w (i.succAbove j) = x (i.succAbove j) :=
      Function.update_of_ne (Fin.succAbove_ne i j) _ _
    have hzsame : zval i.castSucc = lo := Fin.insertNth_apply_same _ _ _
    have hzabove (k : Fin (n + 1)) : zval (i.castSucc.succAbove k) = w k :=
      Fin.insertNth_apply_succAbove _ _ _ _
    have hzval : zval ∈ stdSimplex Real (Fin (n + 2)) := by
      constructor
      · intro j
        by_cases hj : j = i.castSucc
        · subst j
          change 0 ≤ zval i.castSucc
          rw [hzsame]
          exact hlo
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
          change 0 ≤ zval (i.castSucc.succAbove k)
          rw [hzabove]
          by_cases hk : k = i
          · subst k
            rw [hwi]
            exact hhi
          · change 0 ≤ Function.update (fun k => x k) i hi k
            rw [Function.update_of_ne hk]
            exact x.property.1 k
      · rw [Fin.sum_univ_succAbove _ i.castSucc]
        change zval i.castSucc + (∑ k : Fin (n + 1), zval (i.castSucc.succAbove k)) = 1
        simp only [hzsame, hzabove]
        rw [Fin.sum_univ_succAbove w i, hwi]
        change lo + (hi + ∑ j : Fin n, w (i.succAbove j)) = 1
        simp only [hw]
        rw [← add_assoc, hsum]
        exact (Fin.sum_univ_succAbove x.val i).symm.trans x.property.2
    let z : stdSimplex Real (Fin (n + 2)) := ⟨zval, hzval⟩
    have hspatial : stdSimplex.map i.predAbove z = x := by
      apply Subtype.ext
      funext j
      change FunOnFinite.linearMap Real Real i.predAbove z.val j = x j
      rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter,
        Fin.sum_univ_succAbove _ i.castSucc]
      change (if i.predAbove i.castSucc = j then zval i.castSucc else 0) +
        (∑ k : Fin (n + 1), if i.predAbove (i.castSucc.succAbove k) = j then
          zval (i.castSucc.succAbove k) else 0) = x j
      simp only [Fin.predAbove_castSucc_self, Fin.predAbove_succAbove,
        hzsame, hzabove, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      by_cases hj : j = i
      · subst j
        rw [if_pos rfl, hwi]
        exact hsum
      · rw [if_neg (Ne.symm hj), zero_add]
        exact Function.update_of_ne hj _ _
    have htime : (∑ k : Fin (n + 2), if i.castSucc < k then z k else 0) = (t : Real) := by
      rw [Fin.sum_univ_succAbove _ i.castSucc]
      simp only [lt_self_iff_false, if_false, zero_add]
      have hfold : (∑ k : Fin (n + 1),
          if i.castSucc < i.castSucc.succAbove k then z (i.castSucc.succAbove k) else 0) =
          ∑ k : Fin (n + 1), if i ≤ k then w k else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [Fin.lt_succAbove_iff_le_castSucc, Fin.castSucc_le_castSucc_iff]
        change (if i ≤ k then zval (i.castSucc.succAbove k) else 0) = _
        rw [hzabove]
      rw [hfold, Fin.sum_univ_succAbove _ i]
      simp only [le_rfl, if_true]
      rw [hwi]
      change hi + (∑ j : Fin n, if i ≤ i.succAbove j then w (i.succAbove j) else 0) = (t : Real)
      have htail : (∑ j : Fin n, if i ≤ i.succAbove j then w (i.succAbove j) else 0) = S i := by
        dsimp only [S]
        rw [Fin.sum_univ_succAbove _ i]
        simp only [lt_self_iff_false, if_false, zero_add]
        apply Finset.sum_congr rfl
        intro j _
        rw [hw]
        have hne : i.val ≠ (i.succAbove j).val :=
          fun h => Fin.succAbove_ne i j (Fin.ext h.symm)
        by_cases hij : i < i.succAbove j
        · rw [if_pos hij.le, if_pos hij]
        · have hle : ¬i ≤ i.succAbove j := by
            change ¬i.val ≤ (i.succAbove j).val
            change ¬i.val < (i.succAbove j).val at hij
            omega
          rw [if_neg hle, if_neg hij]
      rw [htail]
      exact sub_add_cancel (t : Real) (S i)
    refine ⟨⟨i, z⟩, ?_⟩
    apply Prod.ext hspatial
    exact Subtype.ext htime
  have hQ := _root_.Topology.IsQuotientMap.of_surjective_continuous hsurj Q.continuous
  let g : C(D, X) := ⟨fun z => f z.1 z.2, continuous_sigma (fun i => (f i).continuous)⟩
  have hfac : Function.FactorsThrough g Q := by
    intro z w hzw
    exact hf z.1 w.1 z.2 w.2 hzw
  let F := hQ.lift g hfac
  have hcomp : F.comp Q = g := hQ.lift_comp g hfac
  refine ⟨F, fun i => ?_⟩
  ext z
  have hz := DFunLike.congr_fun hcomp ⟨i, z⟩
  exact hz

end PoincareConjecture.Proofs.M02.Topology
