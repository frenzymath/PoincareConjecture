import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_surgeryCap_compression_widths
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (C : SurgeryCapTag psi u) (c d : ℝ)
    (hrd : C.removal < d) (hdc : d < |C.cutHeight - c|) :
    ∃ o w R : ℝ,
      0 < o ∧ o ≤ C.overlapWidth / 4 ∧ 2 * o < C.overlapWidth ∧
      0 < w ∧ w ≤ C.collarWidth / 4 ∧ 2 * w < C.collarWidth ∧
      0 < R ∧ d ≤ R ∧ R < |C.cutHeight - c| ∧
      (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 2 * o →
        |C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2) -
          C.cutHeight| ≤ R) ∧
      (∀ s : ℝ, |s| ≤ 2 * w →
        |C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s -
          C.cutHeight| ≤ R) := by
  let g := |C.cutHeight - c| - C.removal
  have hg : 0 < g := by dsimp [g]; linarith
  let o := min (C.overlapWidth / 4) (g / (8 * C.scale))
  let w := min (C.collarWidth / 4) (g / (8 * |C.beta|))
  let R := max d (C.removal + g / 2)
  have hbeta : 0 < |C.beta| := abs_pos.mpr C.beta_ne
  have ho : 0 < o := lt_min (div_pos C.overlap_pos (by norm_num))
    (div_pos hg (mul_pos (by norm_num) C.scale_pos))
  have hoo : o ≤ C.overlapWidth / 4 := min_le_left _ _
  have hog : o * (8 * C.scale) ≤ g :=
    (le_div_iff₀ (mul_pos (by norm_num) C.scale_pos)).mp (min_le_right _ _)
  have hw : 0 < w := lt_min (div_pos C.collar_pos (by norm_num))
    (div_pos hg (mul_pos (by norm_num) hbeta))
  have hww : w ≤ C.collarWidth / 4 := min_le_left _ _
  have hwg : w * (8 * |C.beta|) ≤ g :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hdR : d ≤ R := le_max_left _ _
  have hrR : C.removal + g / 2 ≤ R := le_max_right _ _
  have hR : 0 < R := lt_of_lt_of_le (lt_trans C.removal_pos hrd) hdR
  have hRc : R < |C.cutHeight - c| := max_lt hdc (by dsimp [g]; linarith)
  refine ⟨o, w, R, ho, hoo, ?_, hw, hww, ?_, hR, hdR, hRc, ?_, ?_⟩
  · linarith [C.overlap_pos]
  · linarith [C.collar_pos]
  · intro q hq
    by_cases hqs : (heightCoordinates (q : E3)).2 ≤ 0
    · have h := surgeryCapCoordinates_south_height_bounds
        C.profile.horizontal C.profile.vertical C.profile.horizontal_smooth
        C.profile.vertical_smooth (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.vertical_pos
        C.cutHeight C.sign C.removal C.scale C.profile.heightBound
        C.sign_abs C.scale_pos C.scale_small q hqs (C.profile.height_bound q)
      change 3 * C.removal / 4 < C.sign *
          (C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2) -
            C.cutHeight) ∧ C.sign *
          (C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2) -
            C.cutHeight) ≤ C.removal at h
      calc
        _ = |C.sign * (C.cutHeight + C.sign *
            (C.removal + C.scale * (C.profile.model q).2) - C.cutHeight)| := by
          rw [abs_mul, C.sign_abs, one_mul]
        _ = C.sign * (C.cutHeight + C.sign *
            (C.removal + C.scale * (C.profile.model q).2) - C.cutHeight) :=
          abs_of_nonneg (by linarith [C.removal_pos])
        _ ≤ C.removal := h.2
        _ ≤ R := by linarith
    · have hqpos : 0 < (heightCoordinates (q : E3)).2 := lt_of_not_ge hqs
      have hqsmall : |(heightCoordinates (q : E3)).2| ≤ 1 / 4 := by
        rw [abs_of_pos hqpos]
        linarith [C.overlap_le]
      have hmodel := congrArg Prod.snd (surgeryCapModel_cylinder
        C.profile.horizontal C.profile.vertical C.profile.horizontal_smooth
        C.profile.vertical_smooth (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far q hqsmall)
      change (C.profile.model q).2 = (heightCoordinates (q : E3)).2 at hmodel
      rw [hmodel, add_sub_cancel_left, abs_mul, C.sign_abs, one_mul,
        abs_of_pos (add_pos C.removal_pos (mul_pos C.scale_pos hqpos))]
      have hmul := mul_le_mul_of_nonneg_left hq C.scale_pos.le
      nlinarith
  · intro s hs
    have hscale : C.scale ≤ C.scale * C.profile.heightBound := by
      nlinarith [C.profile.one_le_heightBound, C.scale_pos]
    have hsub : 0 ≤ C.removal - C.scale := by
      linarith [C.scale_small, C.removal_pos]
    have hmul := mul_le_mul_of_nonneg_left hs hbeta.le
    calc
      _ = |C.sign * (C.removal - C.scale) + C.beta * s| := by congr 1; ring
      _ ≤ |C.sign * (C.removal - C.scale)| + |C.beta * s| := abs_add_le _ _
      _ = C.removal - C.scale + |C.beta| * |s| := by
        rw [abs_mul, C.sign_abs, one_mul, abs_of_nonneg hsub, abs_mul]
      _ ≤ R := by nlinarith [C.scale_pos]




theorem exists_finite_surgeryCap_compression_buffers
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (c : ℝ) (n : ℕ)
    (C : Fin n → SurgeryCapTag psi u) (d : Fin n → ℝ)
    (hrd : ∀ i, (C i).removal < d i)
    (hdc : ∀ i, d i < |(C i).cutHeight - c|) :
    ∃ o w R : Fin n → ℝ,
      (∀ i,
        0 < o i ∧ o i ≤ (C i).overlapWidth / 4 ∧
        2 * o i < (C i).overlapWidth ∧
        0 < w i ∧ w i ≤ (C i).collarWidth / 4 ∧
        2 * w i < (C i).collarWidth ∧
        0 < R i ∧ d i ≤ R i ∧ R i < |(C i).cutHeight - c| ∧
        (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 2 * o i →
          |(C i).cutHeight + (C i).sign *
              ((C i).removal + (C i).scale * ((C i).profile.model q).2) -
            (C i).cutHeight| ≤ R i) ∧
        (∀ s : ℝ, |s| ≤ 2 * w i →
          |(C i).cutHeight + (C i).sign * ((C i).removal - (C i).scale) +
            (C i).beta * s - (C i).cutHeight| ≤ R i)) ∧
      (let J : Set ℝ := ⋃ i, Metric.closedBall (C i).cutHeight (R i)
       let Q : Set E3 := psi '' (Set.univ ×ˢ ({0} : Set ℝ)) ∪
         ⋃ i, (C i).tube ''
           (Metric.closedBall (0 : E2) 1 ×ˢ Metric.closedBall (C i).cutHeight (R i))
       IsCompact J ∧ c ∉ J ∧ IsCompact Q ∧
       psi '' (Set.univ ×ˢ ({0} : Set ℝ)) ⊆ Q ∧
       ∀ i,
         Metric.closedBall (C i).cutHeight (R i) ⊆ J ∧
         (C i).tube ''
           (Metric.closedBall (0 : E2) 1 ×ˢ Metric.closedBall (C i).cutHeight (R i))
           ⊆ Q ∧
         (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 2 * o i →
           (C i).cutHeight + (C i).sign *
               ((C i).removal + (C i).scale * ((C i).profile.model q).2) ∈ J ∧
             psi ((C i).sourceChart q, 0) ∈ Q) ∧
         (∀ x : E2, ‖x‖ ≤ 1 / 8 → ∀ s : ℝ, |s| ≤ 2 * w i →
           (C i).cutHeight + (C i).sign * ((C i).removal - (C i).scale) +
               (C i).beta * s ∈ J ∧
             psi ((C i).flatChart x, s) ∈ Q)) := by
  choose o w R h using fun i =>
    exists_surgeryCap_compression_widths psi u (C i) c (d i) (hrd i) (hdc i)
  refine ⟨o, w, R, h, ?_⟩
  dsimp only
  have hS : IsCompact (psi '' (univ ×ˢ ({0} : Set ℝ))) := by
    have heq : psi '' (univ ×ˢ ({0} : Set ℝ)) =
        range (fun q : UnitTwoSphere => psi (q, 0)) := by
      ext y
      constructor
      · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
        obtain rfl : t = 0 := ht
        exact mem_range_self q
      · rintro ⟨q, rfl⟩
        exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    rw [heq]
    exact isCompact_range (collar_central_contMDiff psi hpsi).continuous
  have hT (i : Fin n) : IsCompact ((C i).tube ''
      (closedBall (0 : E2) 1 ×ˢ closedBall (C i).cutHeight (R i))) :=
    ((isCompact_closedBall (0 : E2) 1).prod
      (isCompact_closedBall (C i).cutHeight (R i))).image_of_continuousOn
        ((C i).tube.continuousOn.mono (fun _ hp =>
          (C i).tube_source ⟨hp.1, mem_univ _⟩))
  refine ⟨isCompact_iUnion (fun i => isCompact_closedBall _ _), ?_,
    hS.union (isCompact_iUnion hT), subset_union_left, ?_⟩
  · intro hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    have hci : |(C i).cutHeight - c| ≤ R i := by
      simpa only [mem_closedBall, Real.dist_eq, abs_sub_comm] using hi
    exact (not_le_of_gt (h i).2.2.2.2.2.2.2.2.1) hci
  · intro i
    rcases h i with ⟨_, _, hoo, _, _, hww, _, _, _, hcap, hcol⟩
    have hJ : closedBall (C i).cutHeight (R i) ⊆
        ⋃ j, closedBall (C j).cutHeight (R j) := by
      intro y hy
      exact mem_iUnion.mpr ⟨i, hy⟩
    have hQ : (C i).tube ''
        (closedBall (0 : E2) 1 ×ˢ closedBall (C i).cutHeight (R i)) ⊆
        psi '' (univ ×ˢ ({0} : Set ℝ)) ∪ ⋃ j, (C j).tube ''
          (closedBall (0 : E2) 1 ×ˢ closedBall (C j).cutHeight (R j)) := by
      intro y hy
      exact Or.inr (mem_iUnion.mpr ⟨i, hy⟩)
    refine ⟨hJ, hQ, ?_, ?_⟩
    · intro q hq
      have hz : (C i).cutHeight + (C i).sign *
          ((C i).removal + (C i).scale * ((C i).profile.model q).2) ∈
          closedBall (C i).cutHeight (R i) := by
        simpa only [mem_closedBall, Real.dist_eq] using hcap q hq
      refine ⟨hJ hz, ?_⟩
      rw [(C i).central_eq q (lt_of_le_of_lt hq hoo), SurgeryCapProfile.capMap_apply]
      exact hQ ⟨_, ⟨by simpa only [mem_closedBall, dist_zero_right] using
        (C i).profile.model_fst_norm_le q, hz⟩, rfl⟩
    · intro x hx s hs
      have hz : (C i).cutHeight + (C i).sign * ((C i).removal - (C i).scale) +
          (C i).beta * s ∈ closedBall (C i).cutHeight (R i) := by
        simpa only [mem_closedBall, Real.dist_eq] using hcol s hs
      refine ⟨hJ hz, ?_⟩
      rw [(C i).collar_eq x hx s (lt_of_le_of_lt hs hww)]
      exact hQ ⟨_, ⟨by simpa only [mem_closedBall, dist_zero_right] using
        (show ‖x‖ ≤ (1 : ℝ) by linarith), hz⟩, rfl⟩

end PoincareConjecture.M25.Topology3D
