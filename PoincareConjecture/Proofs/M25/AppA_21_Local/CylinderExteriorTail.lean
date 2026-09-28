import PoincareConjecture.Proofs.M25.AppA_21_Local.CapChainAttachment











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem OpenCylinderModel.exists_tail_subset_of_compact_frontier
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {U A : Set M} (T : OpenCylinderModel U)
    (hA : IsOpen A) (hfront : IsCompact (frontier A))
    (hfrontU : frontier A ⊆ U)
    (y : M) (hyA : y ∈ A) (hyclosure : y ∈ closure U) (hyout : y ∉ U) :
    ∃ side : Bool, ∃ a ∈ Ioo (0 : ℝ) 1, T.tail side a ⊆ A := by
  classical
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let h : M → ℝ := fun x => (T.inverse x).2
  have hcont : ContinuousOn h U := T.inverse_smooth.continuousOn.snd
  have hmap {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
      T.coordinate z ∈ U := by
    have hm := (T.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
    rwa [T.coordinate_eq] at hm
  have htail (side : Bool) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (x : M) :
      x ∈ T.tail side r ↔ x ∈ U ∧ (if side then r < h x else h x < r) := by
    cases side
    · simp only [OpenCylinderModel.tail, Bool.false_eq_true, if_false]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzs : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
          ⟨mem_univ _, hz.2.1, hz.2.2.trans hr.2⟩
        refine ⟨hmap hzs, ?_⟩
        change (T.inverse (T.coordinate z)).2 < r
        rw [T.left_inverse hzs]
        exact hz.2.2
      · rintro ⟨hx, hxr⟩
        exact ⟨T.inverse x, ⟨mem_univ _, (T.inverse_mem x hx).2.1, hxr⟩,
          T.right_inverse hx⟩
    · simp only [OpenCylinderModel.tail, if_true]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzs : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
          ⟨mem_univ _, hr.1.trans hz.2.1, hz.2.2⟩
        refine ⟨hmap hzs, ?_⟩
        change r < (T.inverse (T.coordinate z)).2
        rw [T.left_inverse hzs]
        exact hz.2.1
      · rintro ⟨hx, hrx⟩
        exact ⟨T.inverse x, ⟨mem_univ _, hrx, (T.inverse_mem x hx).2.2⟩,
          T.right_inverse hx⟩
  have hbandConnected {p q : ℝ} (hp : 0 ≤ p) (hq : q ≤ 1) (hpq : p < q) :
      IsConnected (T.coordinate '' (univ ×ˢ Ioo p q)) := by
    apply (isConnected_univ.prod (isConnected_Ioo hpq)).image
    exact T.coordinate_smooth.continuousOn.mono
      (fun _ hz => ⟨mem_univ _, hp.trans_lt hz.2.1, hz.2.2.trans_le hq⟩)
  have htailConnected (side : Bool) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
      IsConnected (T.tail side r) := by
    cases side
    · exact hbandConnected le_rfl hr.2.le hr.1
    · exact hbandConnected hr.1.le le_rfl hr.2
  have hfrontCont : ContinuousOn h (frontier A) := hcont.mono hfrontU
  obtain ⟨l, hl, hlFront⟩ := hfront.exists_forall_le' hfrontCont
    (a := (0 : ℝ)) (fun x hx => (T.inverse_mem x (hfrontU hx)).2.1)
  obtain ⟨v, hv, hvFront⟩ := hfront.exists_forall_le' hfrontCont.neg
    (a := (-1 : ℝ)) (fun x hx => by
      have hx1 := (T.inverse_mem x (hfrontU hx)).2.2
      change -1 < -h x
      dsimp only [h]
      linarith)
  obtain ⟨a, ha, haMin⟩ :=
    exists_between (lt_min hl (by norm_num : (0 : ℝ) < 1 / 3))
  have hal : a < l := haMin.trans_le (min_le_left _ _)
  have haThird : a < (1 / 3 : ℝ) := haMin.trans_le (min_le_right _ _)
  have hv1 : -v < (1 : ℝ) := by linarith
  obtain ⟨b, hbMax, hb⟩ :=
    exists_between (max_lt hv1 (by norm_num : (2 / 3 : ℝ) < 1))
  have hvb : -v < b := (le_max_left _ _).trans_lt hbMax
  have hbThird : (2 / 3 : ℝ) < b := (le_max_right _ _).trans_lt hbMax
  have hab : a < b := by linarith
  have ha01 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hb01 : b ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have hfrontBounds (x : M) (hx : x ∈ frontier A) : a < h x ∧ h x < b := by
    refine ⟨hal.trans_le (hlFront x hx), ?_⟩
    have hxNeg : v ≤ -(h x) := hvFront x hx
    have hxUpper : h x ≤ -v := by linarith
    exact hxUpper.trans_lt hvb
  let J := T.coordinate '' (univ ×ˢ Icc a b)
  have hdom : (univ : Set UnitTwoSphere) ×ˢ Icc a b ⊆
      univ ×ˢ Ioo (0 : ℝ) 1 :=
    fun _ hz => ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
  have hJ : IsCompact J :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (T.coordinate_smooth.continuousOn.mono hdom)
  have hJU : J ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact hmap (hdom hz)
  have hyJ : y ∉ J := fun hy => hyout (hJU hy)
  obtain ⟨x, ⟨hxA, hxJ⟩, hxU⟩ :=
    mem_closure_iff.mp hyclosure (A ∩ Jᶜ)
      (hA.inter hJ.isClosed.isOpen_compl) ⟨hyA, hyJ⟩
  have hfinish (side : Bool) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
      (hxTail : x ∈ T.tail side r)
      (havoid : Disjoint (T.tail side r) (frontier A)) :
      ∃ side : Bool, ∃ a ∈ Ioo (0 : ℝ) 1, T.tail side a ⊆ A := by
    have hcover : T.tail side r ⊆ A ∪ (closure A)ᶜ := by
      intro z hz
      by_cases hzA : z ∈ A
      · exact Or.inl hzA
      · refine Or.inr fun hzcl => ?_
        apply disjoint_left.mp havoid hz
        rw [hA.frontier_eq]
        exact ⟨hzcl, hzA⟩
    rcases (htailConnected side hr).isPreconnected.subset_or_subset hA
        isClosed_closure.isOpen_compl
        (disjoint_left.mpr (fun _ hzA hzout => hzout (subset_closure hzA)))
        hcover with hsub | hsub
    · exact ⟨side, r, hr, hsub⟩
    · exact False.elim (hsub hxTail (subset_closure hxA))
  by_cases hxa : h x < a
  · apply hfinish false ha01 ((htail false ha01 x).mpr ⟨hxU, hxa⟩)
    apply disjoint_left.mpr
    intro z hz hzFront
    exact lt_asymm (hfrontBounds z hzFront).1 ((htail false ha01 z).mp hz).2
  · have hbx : b < h x := by
      by_contra hnot
      apply hxJ
      exact ⟨T.inverse x,
        ⟨mem_univ _, le_of_not_gt hxa, le_of_not_gt hnot⟩,
        T.right_inverse hxU⟩
    apply hfinish true hb01 ((htail true hb01 x).mpr ⟨hxU, hbx⟩)
    apply disjoint_left.mpr
    intro z hz hzFront
    exact lt_asymm ((htail true hb01 z).mp hz).2 (hfrontBounds z hzFront).2

end PoincareConjecture
