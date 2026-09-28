import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonCapExteriorFilling
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

set_option autoImplicit false

open Set Function Filter Metric
open scoped Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_common_exterior_half_strip
    (B : Fin 4 → BallNeighborhoodChart E2 E2)
    (c : Fin 4 → UnitCircle → E2)
    (hc : ∀ i, IsPlanarEmbedding (c i))
    (hboundary : ∀ i, (B i).boundary = range (c i))
    (Z : OpenPartialHomeomorph UnitCircle ℝ)
    (gamma : ℝ → E2) (a b l r : ℝ)
    (hal : a < l) (hlr : l < r) (hrb : r < b)
    (hZtarget : Z.target = Ioo a b)
    (hcommon : ∀ i p, p ∈ Z.source → c i p = gamma (Z p))
    (N : OpenPartialHomeomorph (ℝ × ℝ) E2)
    (hNsource : Ioo a b ×ˢ ({0} : Set ℝ) ⊆ N.source)
    (hNzero : ∀ t ∈ Ioo a b, N (t, 0) = gamma t)
    (t0 : ℝ) (ht0 : t0 ∈ Ioo l r)
    (path : ℝ → E2) (hpath : ContinuousAt path 0)
    (hpath0 : path 0 = gamma t0)
    (d : ℝ) (hd : 0 < d)
    (houtside : ∀ t ∈ Ioo (0 : ℝ) d, ∀ i,
      path t ∈ (B i).closedRegionᶜ) :
    ∃ (w sigma : ℝ),
      0 < w ∧ (sigma = 1 ∨ sigma = -1) ∧
      Icc l r ×ˢ Icc (-w) w ⊆ N.source ∧
      ∀ i, N '' (Ioo l r ×ˢ {s : ℝ | 0 < sigma * s ∧ |s| < w}) ⊆
        (B i).closedRegionᶜ := by
  classical
  have hsub : Icc l r ⊆ Ioo a b :=
    fun _ ht => ⟨hal.trans_le ht.1, ht.2.trans_lt hrb⟩
  have hzin (t : ℝ) (ht : t ∈ Ioo a b) : t ∈ Z.target := hZtarget.symm ▸ ht
  have hcg (i : Fin 4) (t : ℝ) (ht : t ∈ Ioo a b) :
      c i (Z.symm t) = gamma t := by
    rw [hcommon i _ (Z.map_target (hzin t ht)), Z.right_inv (hzin t ht)]
  have hgb (i : Fin 4) (t : ℝ) (ht : t ∈ Ioo a b) :
      gamma t ∈ (B i).boundary := by
    rw [hboundary i]
    exact ⟨Z.symm t, hcg i t ht⟩
  let Bad : Set E2 := ⋃ i : Fin 4, c i '' Z.sourceᶜ
  have hBad : IsCompact Bad := isCompact_iUnion (fun i =>
    Z.open_source.isClosed_compl.isCompact.image (hc i).1.continuous)
  have hgBad (t : ℝ) (ht : t ∈ Icc l r) : gamma t ∉ Bad := by
    intro htBad
    obtain ⟨i, p, hp, hpt⟩ := mem_iUnion.mp htBad
    have heq : p = Z.symm t := (hc i).2.1 (hpt.trans (hcg i t (hsub ht)).symm)
    exact hp (heq ▸ Z.map_target (hzin t (hsub ht)))
  let Q : Set (ℝ × ℝ) := Icc l r ×ˢ ({0} : Set ℝ)
  let V : Set (ℝ × ℝ) := N.source ∩ N ⁻¹' Badᶜ
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_singleton
  have hV : IsOpen V := N.isOpen_inter_preimage hBad.isClosed.isOpen_compl
  have hQV : Q ⊆ V := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := mem_singleton_iff.mp hs
    subst s
    refine ⟨hNsource ⟨hsub ht, mem_singleton _⟩, ?_⟩
    change N (t, 0) ∉ Bad
    rw [hNzero t (hsub ht)]
    exact hgBad t ht
  obtain ⟨delta, hdelta, hdV⟩ := hQ.exists_thickening_subset_open hV hQV
  let w : ℝ := delta / 2
  have hw : 0 < w := half_pos hdelta
  have hrect : Icc l r ×ˢ Icc (-w) w ⊆ V := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hdV
    apply mem_thickening_iff.mpr
    refine ⟨(t, 0), ⟨ht, mem_singleton _⟩, ?_⟩
    rw [dist_prod_same_left, Real.dist_eq, sub_zero]
    have hsw : |s| ≤ w := abs_le.mpr hs
    dsimp only [w] at hsw
    linarith
  have hmiss (i : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ Icc l r ×ˢ Icc (-w) w) (hs : p.2 ≠ 0) :
      N p ∉ (B i).boundary := by
    intro hb
    rw [hboundary i] at hb
    obtain ⟨q, hq⟩ := hb
    have hqZ : q ∈ Z.source := by
      by_contra hqZ
      exact (hrect hp).2 (mem_iUnion.mpr ⟨i, q, hqZ, hq⟩)
    have ht : Z q ∈ Ioo a b := hZtarget ▸ Z.map_source hqZ
    have heq : N p = N (Z q, 0) :=
      hq.symm.trans ((hcommon i q hqZ).trans (hNzero (Z q) ht).symm)
    exact hs (congrArg Prod.snd (N.injOn (hrect hp).1
      (hNsource ⟨ht, mem_singleton _⟩) heq))
  let O : Set E2 := N.target ∩ N.symm ⁻¹' (Ioo l r ×ˢ Ioo (-w) w)
  have hO : IsOpen O := N.isOpen_inter_preimage_symm (isOpen_Ioo.prod isOpen_Ioo)
  have ht0ab : t0 ∈ Ioo a b := hsub ⟨ht0.1.le, ht0.2.le⟩
  have ht0N : (t0, (0 : ℝ)) ∈ N.source := hNsource ⟨ht0ab, mem_singleton _⟩
  have h0O : path 0 ∈ O := by
    rw [hpath0, ← hNzero t0 ht0ab]
    refine ⟨N.map_source ht0N, ?_⟩
    change N.symm (N (t0, 0)) ∈ Ioo l r ×ˢ Ioo (-w) w
    rw [N.left_inv ht0N]
    exact ⟨ht0, neg_neg_of_pos hw, hw⟩
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, path t ∈ O := hpath.eventually (hO.mem_nhds h0O)
  obtain ⟨epsilon, hepsilon, heps⟩ := Metric.mem_nhds_iff.mp hevent
  let v : ℝ := min (d / 2) (epsilon / 2)
  have hv : 0 < v := lt_min (half_pos hd) (half_pos hepsilon)
  have hvd : v < d := (min_le_left _ _).trans_lt (by linarith)
  have hve : v < epsilon := (min_le_right _ _).trans_lt (by linarith)
  have hvO : path v ∈ O := by
    apply heps
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hv]
    exact hve
  let p : ℝ × ℝ := N.symm (path v)
  have hpcoord : p ∈ Ioo l r ×ˢ Ioo (-w) w := hvO.2
  have hpN : N p = path v := N.right_inv hvO.1
  have hpnonzero : p.2 ≠ 0 := by
    intro hpzero
    have ht : p.1 ∈ Ioo a b := hsub ⟨hpcoord.1.1.le, hpcoord.1.2.le⟩
    have hpform : p = (p.1, 0) := Prod.ext rfl hpzero
    have hpg : path v = gamma p.1 := by rw [← hpN, hpform, hNzero p.1 ht]
    apply houtside v ⟨hv, hvd⟩ 0
    rw [← (B 0).inside_union_boundary]
    exact Or.inr (hpg.symm ▸ hgb 0 p.1 ht)
  let sigma : ℝ := if 0 < p.2 then 1 else -1
  have hsig : sigma = 1 ∨ sigma = -1 := by
    dsimp only [sigma]
    split_ifs <;> simp
  have hpsign : 0 < sigma * p.2 := by
    dsimp only [sigma]
    split_ifs with hh
    · simpa only [one_mul] using hh
    · rw [neg_one_mul]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hh) hpnonzero)
  let S : Set ℝ := {s : ℝ | 0 < sigma * s ∧ |s| < w}
  have hS : IsPreconnected S := by
    rcases hsig with hsig | hsig
    · have heq : S = Ioo (0 : ℝ) w := by
        ext s
        simp only [S, hsig, one_mul, mem_ofPred_eq, mem_Ioo]
        constructor
        · exact fun hs => ⟨hs.1, (le_abs_self s).trans_lt hs.2⟩
        · exact fun hs => ⟨hs.1, by rw [abs_of_pos hs.1]; exact hs.2⟩
      rw [heq]
      exact isPreconnected_Ioo
    · have heq : S = Ioo (-w) (0 : ℝ) := by
        ext s
        simp only [S, hsig, neg_one_mul, mem_ofPred_eq, mem_Ioo]
        constructor
        · rintro ⟨hs, hw'⟩
          have hs' : s < 0 := neg_pos.mp hs
          rw [abs_of_neg hs'] at hw'
          exact ⟨by linarith, hs'⟩
        · rintro ⟨hs, hs'⟩
          refine ⟨neg_pos.mpr hs', ?_⟩
          rw [abs_of_neg hs']
          linarith
      rw [heq]
      exact isPreconnected_Ioo
  have hSR : Ioo l r ×ˢ S ⊆ Icc l r ×ˢ Icc (-w) w := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    exact ⟨⟨ht.1.le, ht.2.le⟩, abs_le.mp hs.2.le⟩
  have hSN : Ioo l r ×ˢ S ⊆ N.source := fun _ hp => (hrect (hSR hp)).1
  have hpre : IsPreconnected (N '' (Ioo l r ×ˢ S)) :=
    ((isConnected_Ioo hlr).isPreconnected.prod hS).image N (N.continuousOn.mono hSN)
  have hpS : path v ∈ N '' (Ioo l r ×ˢ S) :=
    ⟨p, ⟨hpcoord.1, hpsign, abs_lt.mpr hpcoord.2⟩, hpN⟩
  refine ⟨w, sigma, hw, hsig, fun _ hp => (hrect hp).1, ?_⟩
  intro i
  have hdis : Disjoint (N '' (Ioo l r ×ˢ S)) (B i).boundary := by
    apply disjoint_left.mpr
    rintro _ ⟨q, hq, rfl⟩ hqb
    apply hmiss i q (hSR hq) _ hqb
    intro hzero
    have hh : 0 < sigma * q.2 := hq.2.1
    rw [hzero, mul_zero] at hh
    exact (lt_irrefl _ hh)
  rcases (B i).preconnected_subset_inside_or_outside hpre hdis with hi | ho
  · apply False.elim
    apply houtside v ⟨hv, hvd⟩ i
    rw [← (B i).inside_union_boundary]
    exact Or.inl (hi hpS)
  · exact ho

end PoincareConjecture.M25.Topology3D
