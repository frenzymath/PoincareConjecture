import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapIntersections

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_cap_chord_mem_carrier
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 ≤ r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F ((1 - t) * r, t * r) ∈
      F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
  refine ⟨((1 - t) * r, t * r), ?_, rfl⟩
  exact ⟨mul_nonneg (sub_nonneg.mpr ht.2) hr, mul_nonneg ht.1 hr, by dsimp; nlinarith⟩

theorem m64Intrinsic_cap_open_chord_avoids_axes
    (H F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (i : Bool × Bool) {r : ℝ} (hr : 0 < r)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source)
    (hfirst : ∀ s ∈ Icc (0 : ℝ) r, F (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ s ∈ Icc (0 : ℝ) r, F (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (haxes : (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}) ∩
      H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
      H '' ((sectorParameterEquiv 0 i) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)))) :
    Disjoint ((fun t : ℝ => F ((1 - t) * r, t * r)) '' Ioo (0 : ℝ) 1)
      (H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0})) := by
  apply disjoint_left.mpr
  rintro z ⟨t, ht, rfl⟩ hz
  have hcap := m64Intrinsic_cap_chord_mem_carrier F hr.le (Ioo_subset_Icc_self ht)
  obtain ⟨_, ⟨q, hq, rfl⟩, hqz⟩ := haxes.subset ⟨hcap, hz⟩
  have hsrc : ((1 - t) * r, t * r) ∈ F.source := by
    apply hsource
    exact ⟨mul_nonneg (sub_nonneg.mpr ht.2.le) hr.le, mul_nonneg ht.1.le hr.le,
      by dsimp; nlinarith⟩
  rcases hq with hq | hq
  · have hq0 : q.2 = 0 := hq.2
    have hqeq : q = (q.1, 0) := Prod.ext rfl hq0
    rw [hqeq, ← hfirst q.1 hq.1] at hqz
    have hsrcaxis : (q.1, 0) ∈ F.source :=
      hsource ⟨hq.1.1, le_rfl, by simpa using hq.1.2⟩
    have heq := F.injOn hsrcaxis hsrc hqz
    have h := congrArg Prod.snd heq
    dsimp at h
    exact (mul_pos ht.1 hr).ne' h.symm
  · have hq0 : q.1 = 0 := hq.1
    have hqeq : q = (0, q.2) := Prod.ext hq0 rfl
    rw [hqeq, ← hsecond q.2 hq.2] at hqz
    have hsrcaxis : (0, q.2) ∈ F.source :=
      hsource ⟨le_rfl, hq.2.1, by simpa using hq.2.2⟩
    have heq := F.injOn hsrcaxis hsrc hqz
    have h := congrArg Prod.fst heq
    dsimp at h
    exact (mul_pos (sub_pos.mpr ht.2) hr).ne' h.symm

theorem m64Intrinsic_caps_loop_contacts_in_positive_axes
    {gamma : ℝ → AnnulusCoordinates} {T r : ℝ}
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
    (hsmall : ∀ s ∈ Icc (0 : ℝ) r, (s, 0) ∈ H.source ∧ (0, s) ∈ H.source)
    {A : Set AnnulusCoordinates}
    (hcontact : A ∩ gamma '' Icc 0 T ⊆
      gamma '' Icc 0 r ∪ gamma '' Icc (T - r) T) :
    A ∩ gamma '' Icc 0 T ⊆ H '' (H.source ∩
      {q : ℝ × ℝ | (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)}) := by
  intro z hz
  rcases hcontact hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · exact ⟨(s, 0), ⟨(hsmall s hs).1, Or.inr ⟨hs.1, rfl⟩⟩, haxis s⟩
  · have hs' : T - s ∈ Icc (0 : ℝ) r := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    refine ⟨(0, T - s), ⟨(hsmall (T - s) hs').2, Or.inl ⟨rfl, hs'.1⟩⟩, ?_⟩
    simpa only [sub_sub_cancel] using haxis' (T - s)

theorem m64Intrinsic_cap_chord_loop_contact_parameters
    (H F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (i : Bool × Bool) {r : ℝ} (hr : 0 < r)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source)
    (hfirst : ∀ s ∈ Icc (0 : ℝ) r, F (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ s ∈ Icc (0 : ℝ) r, F (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hsmall : sectorParameterEquiv 0 i (r, 0) ∈ H.source ∧
      sectorParameterEquiv 0 i (0, r) ∈ H.source)
    (haxes : (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}) ∩
      H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
      H '' ((sectorParameterEquiv 0 i) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))))
    {K : Set AnnulusCoordinates}
    (hcontact : (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}) ∩ K ⊆
      H '' (H.source ∩ {q : ℝ × ℝ |
        (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)}))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hpoint : F ((1 - t) * r, t * r) ∈ K) :
    (t = 0 ∧ i.1 = true) ∨ (t = 1 ∧ i.2 = true) := by
  have hp := hcontact ⟨m64Intrinsic_cap_chord_mem_carrier F hr.le ht, hpoint⟩
  have hpaxes : F ((1 - t) * r, t * r) ∈
      H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) := by
    obtain ⟨q, hq, hqz⟩ := hp
    exact ⟨q, ⟨hq.1, hq.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)⟩, hqz⟩
  have hends : t = 0 ∨ t = 1 := by
    by_contra hn
    have hnot := not_or.mp hn
    exact disjoint_left.mp (m64Intrinsic_cap_open_chord_avoids_axes H F i hr
      hsource hfirst hsecond haxes)
      ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hnot.1), lt_of_le_of_ne ht.2 hnot.2⟩, rfl⟩ hpaxes
  obtain ⟨q, hq, hqz⟩ := hp
  rcases hends with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    simp only [sub_zero, one_mul, zero_mul] at hqz
    rw [hfirst r ⟨hr.le, le_rfl⟩] at hqz
    have heq := H.injOn hq.1 hsmall.1 hqz
    have hpos : 0 ≤ q.1 := hq.2.elim (fun h => h.1 ▸ le_rfl) (fun h => h.1)
    rw [heq] at hpos
    cases hi : i.1
    · simp only [sectorParameterEquiv_apply, hi, Bool.false_eq_true, ↓reduceIte,
        Prod.fst_zero, add_zero] at hpos
      linarith
    · rfl
  · right
    refine ⟨rfl, ?_⟩
    simp only [sub_self, zero_mul, one_mul] at hqz
    rw [hsecond r ⟨hr.le, le_rfl⟩] at hqz
    have heq := H.injOn hq.1 hsmall.2 hqz
    have hpos : 0 ≤ q.2 := hq.2.elim (fun h => h.2) (fun h => h.2 ▸ le_rfl)
    rw [heq] at hpos
    cases hi : i.2
    · simp only [sectorParameterEquiv_apply, hi, Bool.false_eq_true, ↓reduceIte,
        Prod.snd_zero, add_zero] at hpos
      linarith
    · rfl

end PoincareConjecture
