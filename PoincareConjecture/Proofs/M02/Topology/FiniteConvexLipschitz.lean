import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith






set_option autoImplicit false

universe u v w

namespace PoincareConjecture.Proofs.M02.Topology

theorem lipschitzOnWith_of_finite_convex_cover
    {E : Type u} {F : Type v} {I : Type w}
    [NormedAddCommGroup E] [NormedSpace Real E] [PseudoMetricSpace F] [Finite I]
    (C : I -> Set E) (hclosed : forall i, IsClosed (C i))
    (hconvex : forall i, Convex Real (C i))
    (U : Set E) (hU : Convex Real U) (hcover : U ⊆ ⋃ i, C i)
    (k : NNReal) (f : E -> F)
    (hf : forall i, LipschitzOnWith k f (C i)) :
    LipschitzOnWith k f U := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let g := AffineMap.lineMap (k := Real) x y
  have hg : Continuous g := (_root_.lipschitzWith_lineMap x y).continuous
  have hgU {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) : g t ∈ U := by
    apply hU.segment_subset hx hy
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  let J (i : I) : Set Real := Set.Icc 0 1 ∩ g ⁻¹' C i
  have hJcompact (i : I) : IsCompact (J i) :=
    isCompact_Icc.inter_right ((hclosed i).preimage hg)
  have hJconvex (i : I) : Convex Real (J i) :=
    (convex_Icc 0 1).inter ((hconvex i).affine_preimage g)
  let S := {i : I | (J i).Nonempty}
  have hS : S.Finite := Set.toFinite S
  let lo (i : I) := sInf (J i)
  let hi (i : I) := sSup (J i)
  have hlo (i : I) (his : i ∈ S) : lo i ∈ J i :=
    (hJcompact i).sInf_mem his
  have hhi (i : I) (his : i ∈ S) : hi i ∈ J i :=
    (hJcompact i).sSup_mem his
  have hbetween (i : I) (his : i ∈ S) {t : Real}
      (ht : lo i ≤ t ∧ t ≤ hi i) : t ∈ J i :=
    (hJconvex i).ordConnected.out (hlo i his) (hhi i his) ht
  let T : Finset Real := {0, 1} ∪ hS.toFinset.biUnion (fun i => {lo i, hi i})
  have hT0 : (0 : Real) ∈ T := by simp [T]
  have hT1 : (1 : Real) ∈ T := by simp [T]
  have hends (i : I) (his : i ∈ S) : lo i ∈ T ∧ hi i ∈ T := by
    constructor <;> apply Finset.mem_union_right _ <;>
      apply Finset.mem_biUnion.mpr <;>
      exact ⟨i, hS.mem_toFinset.mpr his, by simp⟩
  have hT (t : Real) (ht : t ∈ T) : t ∈ Set.Icc (0 : Real) 1 := by
    rcases Finset.mem_union.mp ht with ht | ht
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
    · obtain ⟨i, his, ht⟩ := Finset.mem_biUnion.mp ht
      have hiS := hS.mem_toFinset.mp his
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact (hlo i hiS).1
      · exact (hhi i hiS).1
  let D : Real := (k : Real) * dist x y
  have hstep (a b : Real) (ha : a ∈ T) (hb : b ∈ T) (hab : a < b)
      (hempty : ∀ c ∈ T, ¬(a < c ∧ c < b)) :
      dist (f (g a)) (f (g b)) ≤ (b - a) * D := by
    let t : Real := (a + b) / 2
    have ht : t ∈ Set.Icc (0 : Real) 1 := by
      have ha0 := (hT a ha).1
      have hb1 := (hT b hb).2
      constructor <;> dsimp [t] <;> linarith only [ha0, hb1, hab]
    obtain ⟨i, hit⟩ := Set.mem_iUnion.mp (hcover (hgU ht))
    have hiS : i ∈ S := ⟨t, ht, hit⟩
    have hlot : lo i ≤ t := csInf_le (hJcompact i).bddBelow ⟨ht, hit⟩
    have hthi : t ≤ hi i := le_csSup (hJcompact i).bddAbove ⟨ht, hit⟩
    have hla : lo i ≤ a := by
      by_contra hn
      apply hempty (lo i) (hends i hiS).1
      refine ⟨lt_of_not_ge hn, ?_⟩
      dsimp [t] at hlot
      linarith only [hlot, hab]
    have hbh : b ≤ hi i := by
      by_contra hn
      apply hempty (hi i) (hends i hiS).2
      refine ⟨?_, lt_of_not_ge hn⟩
      dsimp [t] at hthi
      linarith only [hthi, hab]
    have hai := (hbetween i hiS ⟨hla, hab.le.trans hbh⟩).2
    have hbi := (hbetween i hiS ⟨hla.trans hab.le, hbh⟩).2
    have hbound := (hf i).dist_le_mul _ hai _ hbi
    rw [_root_.dist_lineMap_lineMap, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub] at hbound
    simpa only [D, mul_assoc, mul_left_comm] using hbound

  have hchain : ∀ m : Nat, ∀ a b : Real, a ∈ T → b ∈ T → a ≤ b →
      (T.filter (fun t => a < t ∧ t < b)).card = m →
      dist (f (g a)) (f (g b)) ≤ (b - a) * D := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a b ha hb hab hm
      rcases eq_or_lt_of_le hab with rfl | hab
      · simp only [dist_self, sub_self, zero_mul, le_refl]
      by_cases he : (T.filter (fun t => a < t ∧ t < b)).Nonempty
      · obtain ⟨c, hc⟩ := he
        have hcT := (Finset.mem_filter.mp hc).1
        have hac := (Finset.mem_filter.mp hc).2.1
        have hcb := (Finset.mem_filter.mp hc).2.2
        have hl : (T.filter (fun t => a < t ∧ t < c)).card < m := by
          rw [← hm]
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro t ht
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,
              (Finset.mem_filter.mp ht).2.1, (Finset.mem_filter.mp ht).2.2.trans hcb⟩
          · intro heq
            have hmem := heq.symm ▸ hc
            exact (lt_irrefl c) (Finset.mem_filter.mp hmem).2.2
        have hr : (T.filter (fun t => c < t ∧ t < b)).card < m := by
          rw [← hm]
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro t ht
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,
              hac.trans (Finset.mem_filter.mp ht).2.1, (Finset.mem_filter.mp ht).2.2⟩
          · intro heq
            have hmem := heq.symm ▸ hc
            exact (lt_irrefl c) (Finset.mem_filter.mp hmem).2.1
        have hl' := ih _ hl a c ha hcT hac.le rfl
        have hr' := ih _ hr c b hcT hb hcb.le rfl
        have hd := dist_triangle (f (g a)) (f (g c)) (f (g b))
        nlinarith only [hl', hr', hd]
      · apply hstep a b ha hb hab
        intro c hc hmid
        exact he ⟨c, Finset.mem_filter.mpr ⟨hc, hmid⟩⟩
  have hbound := hchain _ 0 1 hT0 hT1 zero_le_one rfl
  simpa only [g, D, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, one_mul] using hbound

end PoincareConjecture.Proofs.M02.Topology
