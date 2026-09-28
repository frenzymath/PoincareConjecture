import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapUnionSeparators












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_cap_attachment_neighborhood
    {gamma : ℝ → AnnulusCoordinates} {T r : ℝ} (hr : 0 < r) (hrT : r < T)
    (hinj : InjOn gamma (Ico 0 T))
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (hbase : H 0 = gamma 0)
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : ∀ i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (F i).source)
    (hFi : ∀ i, ContDiffOn ℝ ∞ (F i).symm (F i).target)
    (hfirst : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2})) (positive terminal : Bool) :
    let selected := if terminal then (positive, true) else (true, positive)
    let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
    let caps (i : Bool × Bool) :=
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    let C := ⋃ i, ⋃ (_ : occupied i), caps i
    ∃ N : Set AnnulusCoordinates,
      IsOpen N ∧ gamma (if terminal then T - r else r) ∈ N ∧
      N ∩ C ⊆ caps selected ∧
      N ∩ frontier (caps selected) ⊆ gamma '' Icc 0 T ∪
        (fun t : ℝ => F selected ((1 - t) * r, t * r)) '' Icc (0 : ℝ) 1 ∧
      F selected (if terminal then (r, 0) else (0, r)) ∉ N := by
  classical
  dsimp only
  let selected := if terminal then (positive, true) else (true, positive)
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let caps (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  obtain ⟨face, hc, hz, ho, ht, _⟩ :=
    m64Intrinsic_exists_coordinate_face_of_chosen_cap (F selected) hr
      (hsource selected) (hF selected) (hFi selected)
  let other : Fin 3 := if terminal then 2 else 1
  let foreign := ⋃ i : Bool × Bool, ⋃ (_ : occupied i ∧ i ≠ selected), caps i
  let K := foreign ∪ (face.boundary other).map '' Icc (0 : ℝ) 1
  have hforeign : IsCompact foreign := isCompact_iUnion (fun i =>
    isCompact_iUnion (fun _ => m64Intrinsic_cap_isCompact (F i) (hsource i)))
  have hK : IsCompact K := hforeign.union
    (isCompact_Icc.image_of_continuousOn (face.boundary other).smooth.continuousOn)
  have htip : F selected (if terminal then (0, r) else (r, 0)) =
      gamma (if terminal then T - r else r) := by
    cases terminal
    · simpa [selected, sectorParameterEquiv_apply, haxis] using
        hfirst (true, positive) r ⟨hr.le, le_rfl⟩
    · simpa [selected, sectorParameterEquiv_apply, haxis'] using
        hsecond (positive, true) r ⟨hr.le, le_rfl⟩
  have hpK : gamma (if terminal then T - r else r) ∉ K := by
    rintro (hpforeign | hpother)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hpforeign
      obtain ⟨⟨hio, hineq⟩, hi⟩ := mem_iUnion.mp hi
      exact hineq (m64Intrinsic_loop_cap_tip_unique hr hrT hinj H hbase haxis haxis'
        F hfirst hsecond hsector positive terminal i hio hi)
    · obtain ⟨t, htr, htp⟩ := hpother
      have htr' : t * r ∈ Icc (0 : ℝ) r :=
        ⟨mul_nonneg htr.1 hr.le, by nlinarith [htr.2]⟩
      rw [← htip] at htp
      cases terminal
      · change (face.boundary 1).map t = F selected (r, 0) at htp
        rw [ho] at htp
        have hs0 : (0, t * r) ∈ (F selected).source :=
          hsource selected ⟨le_rfl, htr'.1, by simpa using htr'.2⟩
        have hs1 : (r, 0) ∈ (F selected).source :=
          hsource selected ⟨hr.le, le_rfl, by simp⟩
        have h := congrArg Prod.fst ((F selected).injOn hs0 hs1 htp)
        exact hr.ne h
      · change (face.boundary 2).map t = F selected (0, r) at htp
        rw [ht] at htp
        have hs0 : (t * r, 0) ∈ (F selected).source :=
          hsource selected ⟨htr'.1, le_rfl, by simpa using htr'.2⟩
        have hs1 : (0, r) ∈ (F selected).source :=
          hsource selected ⟨le_rfl, hr.le, by simp⟩
        have h := congrArg Prod.snd ((F selected).injOn hs0 hs1 htp)
        exact hr.ne h
  refine ⟨Kᶜ, hK.isClosed.isOpen_compl, hpK, ?_, ?_, ?_⟩
  · rintro z ⟨hzK, hzC⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzC
    obtain ⟨hio, hi⟩ := mem_iUnion.mp hi
    by_cases his : i = selected
    · subst i
      exact hi
    · exact False.elim (hzK (Or.inl (mem_iUnion.mpr
        ⟨i, mem_iUnion.mpr ⟨⟨hio, his⟩, hi⟩⟩)))
  · rintro z ⟨hzK, hzfront⟩
    rw [← hc, face.boundary_carrier] at hzfront
    obtain ⟨k, t, htr, rfl⟩ := mem_iUnion.mp hzfront
    by_cases hko : k = other
    · exact False.elim (hzK (Or.inr ⟨t, htr, by rw [hko]⟩))
    by_cases hk0 : k = 0
    · right
      exact ⟨t, htr, by rw [hk0, hz]⟩
    left
    have htr' : t * r ∈ Icc (0 : ℝ) r :=
      ⟨mul_nonneg htr.1 hr.le, by nlinarith [htr.2]⟩
    cases terminal
    · have hk : k = 2 := by fin_cases k <;> simp_all [other]
      rw [hk, ht, hfirst selected _ htr']
      have heq : H (sectorParameterEquiv 0 selected (t * r, 0)) = gamma (t * r) := by
        simp [selected, sectorParameterEquiv_apply, haxis]
      rw [heq]
      exact ⟨t * r, ⟨htr'.1, htr'.2.trans hrT.le⟩, rfl⟩
    · have hk : k = 1 := by fin_cases k <;> simp_all [other]
      rw [hk, ho, hsecond selected _ htr']
      have heq : H (sectorParameterEquiv 0 selected (0, t * r)) = gamma (T - t * r) := by
        simp [selected, sectorParameterEquiv_apply, haxis']
      rw [heq]
      exact ⟨T - t * r, ⟨by linarith [htr'.2], by linarith [htr'.1]⟩, rfl⟩
  · intro hzK
    apply hzK
    right
    refine ⟨1, by norm_num, ?_⟩
    cases terminal
    · change (face.boundary 1).map 1 = F selected (0, r)
      simpa only [one_mul] using ho 1
    · change (face.boundary 2).map 1 = F selected (r, 0)
      simpa only [one_mul] using ht 1

end PoincareConjecture
