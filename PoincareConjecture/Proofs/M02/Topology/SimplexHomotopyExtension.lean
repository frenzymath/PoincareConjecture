import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

open scoped BigOperators

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

def affineSimplexMap {E : Type u}
    [NormedAddCommGroup E] [NormedSpace Real E]
    {n : Nat} (v : Fin (n + 1) -> E) :
    C(stdSimplex Real (Fin (n + 1)), E) :=
  ⟨fun z => ∑ i, z.val i • v i, by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const⟩

theorem exists_affine_simplex_homeomorph {E : Type u}
    [NormedAddCommGroup E] [NormedSpace Real E]
    {n : Nat} (v : Fin (n + 1) -> E) (hv : AffineIndependent Real v) :
    Exists fun e : stdSimplex Real (Fin (n + 1)) ≃ₜ
        convexHull Real (Set.range v) =>
      forall z, (e z).val = affineSimplexMap v z := by
  classical
  have hm (z : stdSimplex Real (Fin (n + 1))) :
      affineSimplexMap v z ∈ convexHull Real (Set.range v) :=
    mem_convexHull_of_exists_fintype z.val v z.property.1 z.property.2
      (fun i => Set.mem_range_self i) rfl
  let F : C(stdSimplex Real (Fin (n + 1)), convexHull Real (Set.range v)) :=
    ⟨fun z => ⟨affineSimplexMap v z, hm z⟩, (affineSimplexMap v).continuous.subtype_mk hm⟩
  have hi : Function.Injective F := by
    intro z w h
    have hsum : ∑ i, z.val i • v i = ∑ i, w.val i • v i :=
      congrArg Subtype.val h
    apply Subtype.ext
    funext i
    exact hv.eq_of_sum_eq_sum
      (z.property.2.trans w.property.2.symm) hsum i (Finset.mem_univ i)
  have hs : Function.Surjective F := by
    intro y
    obtain ⟨s, w, hw, hw1, he⟩ :=
      (show ∃ (s : Finset (Fin (n + 1))) (w : Fin (n + 1) -> Real),
        (∀ i ∈ s, 0 ≤ w i) ∧ s.sum w = 1 ∧ s.affineCombination Real v w = y.val from by
          simpa only [convexHull_range_eq_exists_affineCombination, Set.mem_ofPred_eq]
            using y.property)
    let a : Fin (n + 1) -> Real := fun i => if i ∈ s then w i else 0
    have ha (i : Fin (n + 1)) : 0 ≤ a i := by
      by_cases h : i ∈ s
      · simpa only [a, if_pos h] using hw i h
      · simp only [a, if_neg h, le_refl]
    have ha1 : ∑ i, a i = 1 := by
      calc
        ∑ i, a i = ∑ i ∈ s, a i :=
          (Finset.sum_subset (Finset.subset_univ s)
            (fun i _ h => by simp only [a, if_neg h])).symm
        _ = ∑ i ∈ s, w i := Finset.sum_congr rfl (fun i h => by simp only [a, if_pos h])
        _ = 1 := hw1
    have he' : ∑ i, a i • v i = y.val := by
      calc
        ∑ i, a i • v i = ∑ i ∈ s, a i • v i :=
          (Finset.sum_subset (Finset.subset_univ s)
            (fun i _ h => by simp only [a, if_neg h, zero_smul])).symm
        _ = ∑ i ∈ s, w i • v i :=
          Finset.sum_congr rfl (fun i h => by simp only [a, if_pos h])
        _ = s.affineCombination Real v w :=
          (Finset.affineCombination_eq_linear_combination s v w hw1).symm
        _ = y.val := he
    refine ⟨⟨a, ha, ha1⟩, ?_⟩
    apply Subtype.ext
    exact he'
  let e := Equiv.ofBijective F ⟨hi, hs⟩
  exact ⟨e.toHomeomorphOfContinuousClosed F.continuous F.continuous.isClosedMap, fun _ => rfl⟩

set_option maxHeartbeats 1000000 in

def stdSimplexHomotopyRetract (n : Nat) :
    C(stdSimplex Real (Fin (n + 1)) × unitInterval,
      stdSimplex Real (Fin (n + 1)) × unitInterval) := by
  classical
  let m : Real := n + 1
  let c : Real := 1 / m
  let g (z : stdSimplex Real (Fin (n + 1))) : Real :=
    (Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty
      (fun i => 1 - m * z.val i)
  let d (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : Real :=
    max (1 - (p.2 : Real) / 2) (g p.1)
  let w (p : stdSimplex Real (Fin (n + 1)) × unitInterval) (i : Fin (n + 1)) : Real :=
    c + (p.1.val i - c) / d p
  let t (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : Real :=
    2 + ((p.2 : Real) - 2) / d p
  have hm : 0 < m := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hg (z : stdSimplex Real (Fin (n + 1))) : g z ≤ 1 := by
    apply Finset.sup'_le
    intro i _
    have hz := z.property.1 i
    nlinarith only [hz, hm]
  have hd (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : 1 / 2 ≤ d p ∧ d p ≤ 1 := by
    have hp0 := p.2.property.1
    have hp1 := p.2.property.2
    constructor
    · have hl : (1 / 2 : Real) ≤ 1 - (p.2 : Real) / 2 := by linarith only [hp1]
      exact hl.trans (le_max_left _ _)
    · exact max_le (by linarith only [hp0]) (hg p.1)
  have hdpos (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : 0 < d p :=
    lt_of_lt_of_le (by norm_num) (hd p).1
  have hw0 (p : stdSimplex Real (Fin (n + 1)) × unitInterval) (i : Fin (n + 1)) :
      0 ≤ w p i := by
    have hle : 1 - m * p.1.val i ≤ d p :=
      (Finset.le_sup' (fun j => 1 - m * p.1.val j) (Finset.mem_univ i)).trans
        (le_max_right _ _)
    have he : (m * d p) * w p i = d p + m * p.1.val i - 1 := by
      dsimp only [w, c]
      field_simp [ne_of_gt hm, ne_of_gt (hdpos p)]
      ring
    apply (mul_nonneg_iff_of_pos_left (mul_pos hm (hdpos p))).mp
    rw [he]
    linarith only [hle]
  have hc : (n + 1 : Real) * c = 1 := by
    exact mul_one_div_cancel (ne_of_gt hm)
  have hw1 (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : ∑ i, w p i = 1 := by
    simp only [w, div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, hc, p.1.property.2, sub_self, zero_mul, add_zero]
  have ht (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : t p ∈ unitInterval := by
    have he : d p * t p = 2 * d p + (p.2 : Real) - 2 := by
      dsimp only [t]
      field_simp [ne_of_gt (hdpos p)]
      ring
    constructor
    · apply (mul_nonneg_iff_of_pos_left (hdpos p)).mp
      rw [he]
      have hl := le_max_left (1 - (p.2 : Real) / 2) (g p.1)
      change 1 - (p.2 : Real) / 2 ≤ d p at hl
      linarith only [hl]
    · have hp := p.2.property.2
      have hprod : (2 - (p.2 : Real)) * (d p - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith only [hp]) (sub_nonpos.mpr (hd p).2)
      have hmul : d p * t p ≤ d p * (p.2 : Real) := by nlinarith only [he, hprod]
      have htle : t p ≤ (p.2 : Real) := le_of_mul_le_mul_left hmul (hdpos p)
      exact htle.trans hp
  have hgc : Continuous g := by
    apply Continuous.finset_sup'_apply
    intro i _
    exact continuous_const.sub
      (continuous_const.mul ((continuous_apply i).comp continuous_subtype_val))
  have hpc : Continuous (fun p : stdSimplex Real (Fin (n + 1)) × unitInterval =>
      (p.2 : Real)) := continuous_subtype_val.comp continuous_snd
  have hdc : Continuous d :=
    (continuous_const.sub (hpc.div_const 2)).max (hgc.comp continuous_fst)
  have hwc : Continuous w := by
    apply continuous_pi
    intro i
    exact continuous_const.add
      ((((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).sub
        continuous_const).div hdc (fun p => ne_of_gt (hdpos p)))
  have htc : Continuous t :=
    continuous_const.add ((hpc.sub continuous_const).div hdc (fun p => ne_of_gt (hdpos p)))
  exact ⟨fun p => (⟨w p, hw0 p, hw1 p⟩, ⟨t p, ht p⟩),
    (hwc.subtype_mk (fun p => ⟨hw0 p, hw1 p⟩)).prodMk (htc.subtype_mk ht)⟩

set_option maxHeartbeats 1000000 in

theorem stdSimplexHomotopyRetract_spec (n : Nat) :
    (forall p : stdSimplex Real (Fin (n + 1)) × unitInterval,
      (stdSimplexHomotopyRetract n p).2 = 0 ∨
        Exists fun i : Fin (n + 1) =>
          (stdSimplexHomotopyRetract n p).1 i = 0) ∧
    (forall p : stdSimplex Real (Fin (n + 1)) × unitInterval,
      (p.2 = 0 ∨ Exists fun i : Fin (n + 1) => p.1 i = 0) ->
        stdSimplexHomotopyRetract n p = p) := by
  classical
  let m : Real := n + 1
  let c : Real := 1 / m
  let g (z : stdSimplex Real (Fin (n + 1))) : Real :=
    (Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty
      (fun i => 1 - m * z.val i)
  let d (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : Real :=
    max (1 - (p.2 : Real) / 2) (g p.1)
  have hm : 0 < m := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hg (z : stdSimplex Real (Fin (n + 1))) : g z ≤ 1 := by
    apply Finset.sup'_le
    intro i _
    have hz := z.property.1 i
    nlinarith only [hz, hm]
  have hdpos (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : 0 < d p := by
    have hp := p.2.property.2
    exact lt_of_lt_of_le (by linarith only [hp]) (le_max_left _ _)
  have hdle (p : stdSimplex Real (Fin (n + 1)) × unitInterval) : d p ≤ 1 := by
    have hp := p.2.property.1
    exact max_le (by linarith only [hp]) (hg p.1)
  constructor
  · intro p
    by_cases h : g p.1 ≤ 1 - (p.2 : Real) / 2
    · left
      apply Subtype.ext
      change 2 + ((p.2 : Real) - 2) / d p = 0
      have hdp : d p = 1 - (p.2 : Real) / 2 := max_eq_left h
      have he : d p * (2 + ((p.2 : Real) - 2) / d p) =
          2 * d p + (p.2 : Real) - 2 := by
        field_simp [ne_of_gt (hdpos p)]
        ring
      have hz : 2 * d p + (p.2 : Real) - 2 = 0 := by
        rw [hdp]
        ring
      exact (mul_eq_zero.mp (he.trans hz)).resolve_left (ne_of_gt (hdpos p))
    · right
      obtain ⟨i, _, hi⟩ :=
        Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin (n + 1))))
          Finset.univ_nonempty (fun i => 1 - m * p.1.val i)
      have hdp : d p = 1 - m * p.1.val i :=
        (max_eq_right (le_of_lt (lt_of_not_ge h))).trans hi
      have hn : 1 - m * p.1.val i ≠ 0 := by
        rw [← hdp]
        exact ne_of_gt (hdpos p)
      refine ⟨i, ?_⟩
      change c + (p.1.val i - c) / d p = 0
      rw [hdp]
      dsimp only [c]
      field_simp [ne_of_gt hm, hn]
      ring
  · intro p hp
    have hdp : d p = 1 := by
      apply le_antisymm (hdle p)
      rcases hp with hp | ⟨i, hi⟩
      · have hpt : (p.2 : Real) = 0 := congrArg Subtype.val hp
        have hl := le_max_left (1 - (p.2 : Real) / 2) (g p.1)
        change 1 - (p.2 : Real) / 2 ≤ d p at hl
        simpa only [hpt, zero_div, sub_zero] using hl
      · have hl := Finset.le_sup' (fun j => 1 - m * p.1.val j) (Finset.mem_univ i)
        change 1 - m * p.1.val i ≤ g p.1 at hl
        have hi' : p.1.val i = 0 := hi
        have hl' : (1 : Real) ≤ g p.1 := by
          simpa only [hi', mul_zero, sub_zero] using hl
        exact hl'.trans (le_max_right _ _)
    apply Prod.ext
    · apply Subtype.ext
      funext i
      change c + (p.1.val i - c) / d p = p.1.val i
      rw [hdp, div_one]
      ring
    · apply Subtype.ext
      change 2 + ((p.2 : Real) - 2) / d p = (p.2 : Real)
      rw [hdp, div_one]
      ring

set_option maxHeartbeats 1000000 in

theorem exists_stdSimplex_homotopy_extension
    {X : Type v} [TopologicalSpace X] (n : Nat)
    (f : C(stdSimplex Real (Fin (n + 1)), X))
    (H : C({z : stdSimplex Real (Fin (n + 1)) //
      Exists fun i : Fin (n + 1) => z i = 0} × unitInterval, X))
    (h0 : forall z, H (z, 0) = f z.val) :
    Exists fun F : C(stdSimplex Real (Fin (n + 1)) × unitInterval, X) =>
      (forall z, F (z, 0) = f z) ∧
      (forall z t, F (z.val, t) = H (z, t)) := by
  classical
  let D := stdSimplex Real (Fin (n + 1))
  let B : Set D := {z | ∃ i : Fin (n + 1), z i = 0}
  let A : Set (D × unitInterval) := {p | p.2 = 0 ∨ ∃ i : Fin (n + 1), p.1 i = 0}
  have hB : IsClosed B := by
    have he : B = ⋃ i : Fin (n + 1), {z : D | z i = 0} := by
      ext z
      simp only [B, Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [he]
    apply isClosed_iUnion_of_finite
    intro i
    exact isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const
  have : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let Q : C(D ⊕ (B × unitInterval), A) :=
    ⟨Sum.elim (fun z => ⟨(z, 0), Or.inl rfl⟩)
      (fun p => ⟨(p.1.val, p.2), Or.inr p.1.property⟩), by
        apply continuous_sum_dom.2
        constructor
        · exact (continuous_id.prodMk continuous_const).subtype_mk (fun _ => Or.inl rfl)
        · exact ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk
            (fun p => Or.inr p.1.property)⟩
  have hsurj : Function.Surjective Q := by
    rintro ⟨p, hp⟩
    rcases hp with hp | hp
    · refine ⟨Sum.inl p.1, ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl hp.symm
    · exact ⟨Sum.inr (⟨p.1, hp⟩, p.2), rfl⟩
  let g : C(D ⊕ (B × unitInterval), X) :=
    ⟨Sum.elim f H, continuous_sum_dom.2 ⟨f.continuous, H.continuous⟩⟩
  have hfac : Function.FactorsThrough g Q := by
    intro a b hab
    cases a with
    | inl z =>
      cases b with
      | inl w =>
        exact congrArg f (congrArg (fun p : A => p.val.1) hab)
      | inr p =>
        have hz : z = p.1.val := congrArg (fun p : A => p.val.1) hab
        have ht : (0 : unitInterval) = p.2 := congrArg (fun p : A => p.val.2) hab
        change f z = H p
        exact (congrArg f hz).trans
          ((h0 p.1).symm.trans (congrArg H (Prod.ext rfl ht)))
    | inr p =>
      cases b with
      | inl z =>
        have hz : p.1.val = z := congrArg (fun p : A => p.val.1) hab
        have ht : p.2 = (0 : unitInterval) := congrArg (fun p : A => p.val.2) hab
        change H p = f z
        have he : p = (p.1, (0 : unitInterval)) := Prod.ext rfl ht
        exact (congrArg H he).trans ((h0 p.1).trans (congrArg f hz))
      | inr q =>
        have hz : p.1.val = q.1.val := congrArg (fun p : A => p.val.1) hab
        have ht : p.2 = q.2 := congrArg (fun p : A => p.val.2) hab
        exact congrArg H (Prod.ext (Subtype.ext hz) ht)
  have hQ := _root_.Topology.IsQuotientMap.of_surjective_continuous hsurj Q.continuous
  let G := hQ.lift g hfac
  have hG (z : D ⊕ (B × unitInterval)) : G (Q z) = g z :=
    congrArg (fun k : C(D ⊕ (B × unitInterval), X) => k z) (hQ.lift_comp g hfac)
  let R : C(D × unitInterval, A) :=
    ⟨fun p => ⟨stdSimplexHomotopyRetract n p, (stdSimplexHomotopyRetract_spec n).1 p⟩,
      (stdSimplexHomotopyRetract n).continuous.subtype_mk
        ((stdSimplexHomotopyRetract_spec n).1)⟩
  refine ⟨G.comp R, ?_, ?_⟩
  · intro z
    have he : R (z, 0) = Q (Sum.inl z) := by
      apply Subtype.ext
      exact (stdSimplexHomotopyRetract_spec n).2 (z, 0) (Or.inl rfl)
    change G (R (z, 0)) = f z
    rw [he]
    exact hG (Sum.inl z)
  · intro z t
    have he : R (z.val, t) = Q (Sum.inr (z, t)) := by
      apply Subtype.ext
      exact (stdSimplexHomotopyRetract_spec n).2 (z.val, t) (Or.inr z.property)
    change G (R (z.val, t)) = H (z, t)
    rw [he]
    exact hG (Sum.inr (z, t))

end PoincareConjecture.Proofs.M02.Topology
