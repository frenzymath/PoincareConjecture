import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularThreshold

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_finite_superlevel_intervals
    {f : ℝ → ℝ} (hf : Continuous f) {P alpha : ℝ} (hP : 0 < P)
    (hfinite : {t | t ∈ Icc (0 : ℝ) P ∧ f t = alpha}.Finite) :
    ∃ T : Set (ℝ × ℝ), T.Finite ∧
      (∀ p ∈ T, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ P ∧
        (p.1 = 0 ∨ f p.1 = alpha) ∧ (p.2 = P ∨ f p.2 = alpha)) ∧
      T.PairwiseDisjoint (fun p => Ioo p.1 p.2) ∧
      {t | t ∈ Ioo (0 : ℝ) P ∧ alpha < f t} = ⋃ p ∈ T, Ioo p.1 p.2 := by
  let S : Set ℝ := ({0, P} : Set ℝ) ∪ {t | t ∈ Icc (0 : ℝ) P ∧ f t = alpha}
  have hS : S.Finite := (Set.toFinite {0, P}).union hfinite
  have hzero : (0 : ℝ) ∈ S := Or.inl (by simp)
  have hlast : P ∈ S := Or.inl (by simp)
  have hbounds (t : ℝ) (ht : t ∈ S) : t ∈ Icc (0 : ℝ) P := by
    rcases ht with ht | ht
    · rcases (show t = 0 ∨ t = P by simpa only [mem_insert_iff, mem_singleton_iff] using ht)
        with rfl | rfl
      · exact ⟨le_rfl, hP.le⟩
      · exact ⟨hP.le, le_rfl⟩
    · exact ht.1
  let T : Set (ℝ × ℝ) := {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧
    (∀ t ∈ Ioo p.1 p.2, t ∉ S) ∧ ∀ t ∈ Ioo p.1 p.2, alpha < f t}
  have hT : T.Finite := (hS.prod hS).subset (fun _ hp => ⟨hp.1, hp.2.1⟩)
  have hendpoint (t : ℝ) (ht : t ∈ S) : t = 0 ∨ t = P ∨ f t = alpha := by
    rcases ht with ht | ht
    · exact (show t = 0 ∨ t = P by simpa only [mem_insert_iff, mem_singleton_iff] using ht)
        |>.imp_right Or.inl
    · exact Or.inr (Or.inr ht.2)
  have hTB (p : ℝ × ℝ) (hp : p ∈ T) :
      0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ P ∧
        (p.1 = 0 ∨ f p.1 = alpha) ∧ (p.2 = P ∨ f p.2 = alpha) := by
    have hp1 := hbounds p.1 hp.1
    have hp2 := hbounds p.2 hp.2.1
    refine ⟨hp1.1, hp.2.2.1, hp2.2, ?_, ?_⟩
    · rcases hendpoint p.1 hp.1 with h | h | h
      · exact Or.inl h
      · exact False.elim (by linarith [hp.2.2.1, hp2.2])
      · exact Or.inr h
    · rcases hendpoint p.2 hp.2.1 with h | h | h
      · exact False.elim (by linarith [hp.2.2.1, hp1.1])
      · exact Or.inl h
      · exact Or.inr h
  refine ⟨T, hT, hTB, ?_, ?_⟩
  · intro p hp q hq hpq
    change Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2)
    rw [Set.disjoint_left]
    intro t htp htq
    apply hpq
    have hleft : p.1 = q.1 := by
      rcases lt_trichotomy p.1 q.1 with hlt | heq | hlt
      · exact False.elim ((hp.2.2.2.1 q.1 ⟨hlt, htq.1.trans htp.2⟩) hq.1)
      · exact heq
      · exact False.elim ((hq.2.2.2.1 p.1 ⟨hlt, htp.1.trans htq.2⟩) hp.1)
    have hright : p.2 = q.2 := by
      rcases lt_trichotomy p.2 q.2 with hlt | heq | hlt
      · exact False.elim ((hq.2.2.2.1 p.2 ⟨htq.1.trans htp.2, hlt⟩) hp.2.1)
      · exact heq
      · exact False.elim ((hp.2.2.2.1 q.2 ⟨htp.1.trans htq.2, hlt⟩) hq.2.1)
    exact Prod.ext hleft hright
  · ext t
    constructor
    · intro ht
      have htS : t ∉ S := by
        intro h
        rcases hendpoint t h with h | h | h
        · linarith [ht.1.1]
        · linarith [ht.1.2]
        · exact ht.2.ne' h
      obtain ⟨a, ha, hmax⟩ := (hS.isCompact.inter_right isClosed_Iic).exists_isGreatest
        (show (S ∩ Iic t).Nonempty from ⟨0, hzero, ht.1.1.le⟩)
      obtain ⟨b, hb, hmin⟩ := (hS.isCompact.inter_right isClosed_Ici).exists_isLeast
        (show (S ∩ Ici t).Nonempty from ⟨P, hlast, ht.1.2.le⟩)
      have hat : a < t := lt_of_le_of_ne ha.2 (fun h => htS (h ▸ ha.1))
      have htb : t < b := lt_of_le_of_ne hb.2 (fun h => htS (h.symm ▸ hb.1))
      have hgap (x : ℝ) (hx : x ∈ Ioo a b) : x ∉ S := by
        intro hxS
        by_cases hxt : x ≤ t
        · exact (not_le_of_gt hx.1) (hmax ⟨hxS, hxt⟩)
        · exact (not_le_of_gt hx.2) (hmin ⟨hxS, le_of_not_ge hxt⟩)
      have hhigh (x : ℝ) (hx : x ∈ Ioo a b) : alpha < f x := by
        by_contra hnot
        obtain ⟨y, hy, hfy⟩ := isPreconnected_Ioo.intermediate_value hx ⟨hat, htb⟩
          hf.continuousOn (show alpha ∈ Icc (f x) (f t) from ⟨le_of_not_gt hnot, ht.2.le⟩)
        have hyP : y ∈ Icc (0 : ℝ) P :=
          ⟨(hbounds a ha.1).1.trans hy.1.le, hy.2.le.trans (hbounds b hb.1).2⟩
        exact hgap y hy (Or.inr ⟨hyP, hfy⟩)
      exact mem_iUnion.mpr ⟨(a, b), mem_iUnion.mpr
        ⟨⟨ha.1, hb.1, hat.trans htb, hgap, hhigh⟩, hat, htb⟩⟩
    · intro ht
      obtain ⟨p, ht⟩ := mem_iUnion.mp ht
      obtain ⟨hp, htp⟩ := mem_iUnion.mp ht
      have hpB := hTB p hp
      exact ⟨⟨hpB.1.trans_lt htp.1, htp.2.trans_le hpB.2.2.1⟩, hp.2.2.2.2 t htp⟩

theorem m64Intrinsic_exists_finite_high_curvature_intervals
    (N : IntrinsicAnnulus) {delta r : ℝ} (hdelta : 0 < delta) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r) :
    ∃ alpha ∈ Ioo (100 * delta / r) (110 * delta / r),
      m64IntrinsicHighCurvatureLength N alpha <
        intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 ∧
      ∃ T : Set (ℝ × ℝ), T.Finite ∧
        (∀ p ∈ T, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ rampPeriod ∧
          (p.1 = 0 ∨ intrinsicGeodesicCurvature N.metric N.connection 1 p.1 = alpha) ∧
          (p.2 = rampPeriod ∨ intrinsicGeodesicCurvature N.metric N.connection 1 p.2 = alpha)) ∧
        T.PairwiseDisjoint (fun p => Ioo p.1 p.2) ∧
        {t | t ∈ Ioo (0 : ℝ) rampPeriod ∧
          alpha < intrinsicGeodesicCurvature N.metric N.connection 1 t} =
            ⋃ p ∈ T, Ioo p.1 p.2 := by
  obtain ⟨alpha, halpha, hfinite, _, hloss⟩ :=
    m64Intrinsic_exists_regular_curvature_cutoff N hdelta hr hfirst hturn
  exact ⟨alpha, halpha, hloss, m64Intrinsic_finite_superlevel_intervals
    (m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0))
    (show 0 < rampPeriod from Real.two_pi_pos) hfinite⟩

end PoincareConjecture
