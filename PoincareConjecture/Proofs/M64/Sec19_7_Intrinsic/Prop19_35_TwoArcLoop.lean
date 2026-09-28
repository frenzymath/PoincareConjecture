import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcRegion















noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

private theorem exists_unit_loop_between_arcs
    {alpha beta : ℝ → AnnulusCoordinates}
    (halpha : ContinuousOn alpha (Icc 0 1)) (hbeta : ContinuousOn beta (Icc 0 1))
    (halphaInj : InjOn alpha (Icc 0 1)) (hbetaInj : InjOn beta (Icc 0 1))
    (h0 : alpha 0 = beta 0) (hend : alpha 1 = beta 1)
    (hmeet : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ loop : ℝ → AnnulusCoordinates,
      ContinuousOn loop (Icc 0 2) ∧ loop 0 = loop 2 ∧ InjOn loop (Ico 0 2) ∧
      loop '' Icc 0 2 = alpha '' Icc 0 1 ∪ beta '' Icc 0 1 := by
  classical
  let loop : ℝ → AnnulusCoordinates := fun t => if t ≤ 1 then alpha t else beta (2 - t)
  have hcont : ContinuousOn loop (Icc 0 2) := by
    apply ContinuousOn.if
    · intro t ht
      have ht' : t = 1 := by
        have h := ht.2
        change t ∈ frontier (Iic (1 : ℝ)) at h
        simpa only [frontier_Iic, mem_singleton_iff] using h
      subst t
      convert hend using 1
      norm_num
    · apply halpha.mono
      intro t ht
      exact ⟨ht.1.1, by simpa only [show {a : ℝ | a ≤ 1} = Iic 1 from rfl,
        isClosed_Iic.closure_eq, mem_Iic] using ht.2⟩
    · apply hbeta.comp (continuous_const.sub continuous_id).continuousOn
      intro t ht
      have ht1 : 1 ≤ t := by
        have h := ht.2
        simp only [not_le] at h
        change t ∈ closure (Ioi (1 : ℝ)) at h
        simpa only [closure_Ioi, mem_Ici] using h
      change 2 - t ∈ Icc 0 1
      exact ⟨by linarith [ht.1.2], by linarith⟩
  have hstart : loop 0 = alpha 0 := by norm_num [loop]
  have hfinish : loop 2 = beta 0 := by norm_num [loop]
  have hclosed : loop 0 = loop 2 := hstart.trans (h0.trans hfinish.symm)
  have hinj : InjOn loop (Ico 0 2) := by
    intro s hs t ht heq
    wlog hst : s ≤ t generalizing s t
    · exact (this ht hs heq.symm (le_of_not_ge hst)).symm
    by_cases ht1 : t ≤ 1
    · have hs1 : s ≤ 1 := hst.trans ht1
      apply halphaInj ⟨hs.1, hs1⟩ ⟨ht.1, ht1⟩
      simpa only [loop, if_pos hs1, if_pos ht1] using heq
    · by_cases hs1 : s ≤ 1
      · have h := hmeet s ⟨hs.1, hs1⟩ (2 - t)
          ⟨by linarith [ht.2], by linarith⟩
          (by simpa only [loop, if_pos hs1, if_neg ht1] using heq)
        rcases h with ⟨_, ht0⟩ | ⟨_, ht'⟩
        · linarith [ht.2]
        · linarith
      · have h := hbetaInj (x₁ := 2 - s) (x₂ := 2 - t)
          ⟨by linarith [hs.2], by linarith⟩
          ⟨by linarith [ht.2], by linarith⟩
          (by simpa only [loop, if_neg hs1, if_neg ht1] using heq)
        linarith
  have himage : loop '' Icc 0 2 = alpha '' Icc 0 1 ∪ beta '' Icc 0 1 := by
    apply Subset.antisymm
    · rintro p ⟨t, ht, rfl⟩
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨t, ⟨ht.1, ht1⟩, (if_pos ht1).symm⟩
      · exact Or.inr ⟨2 - t, ⟨by linarith [ht.2], by linarith⟩, (if_neg ht1).symm⟩
    · rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, if_pos ht.2⟩
      · refine ⟨2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
        by_cases ht1 : t = 1
        · subst t
          norm_num [loop]
          exact hend
        · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
          rw [show loop (2 - t) = beta (2 - (2 - t)) from if_neg (by linarith)]
          congr 1
          ring
  exact ⟨loop, hcont, hclosed, hinj, himage⟩





theorem m64Intrinsic_exists_simple_loop_between_arcs
    {alpha beta : ℝ → AnnulusCoordinates} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (halpha : ContinuousOn alpha (Icc 0 A)) (hbeta : ContinuousOn beta (Icc 0 B))
    (halphaInj : InjOn alpha (Icc 0 A)) (hbetaInj : InjOn beta (Icc 0 B))
    (h0 : alpha 0 = beta 0) (hend : alpha A = beta B)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B)) :
    ∃ loop : ℝ → AnnulusCoordinates,
      ContinuousOn loop (Icc 0 2) ∧ loop 0 = loop 2 ∧ InjOn loop (Ico 0 2) ∧
      loop '' Icc 0 2 = alpha '' Icc 0 A ∪ beta '' Icc 0 B := by
  let alphaUnit : ℝ → AnnulusCoordinates := fun s => alpha (A * s)
  let betaUnit : ℝ → AnnulusCoordinates := fun s => beta (B * s)
  have hscale {C : ℝ} (hC : 0 < C) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
      C * s ∈ Icc 0 C :=
    ⟨mul_nonneg hC.le hs.1, by nlinarith [hs.2]⟩
  have halphaUnit : ContinuousOn alphaUnit (Icc 0 1) :=
    halpha.comp (continuous_const.mul continuous_id).continuousOn (fun _ hs => hscale hA hs)
  have hbetaUnit : ContinuousOn betaUnit (Icc 0 1) :=
    hbeta.comp (continuous_const.mul continuous_id).continuousOn (fun _ hs => hscale hB hs)
  have halphaUnitInj : InjOn alphaUnit (Icc 0 1) := by
    intro s hs t ht heq
    exact mul_left_cancel₀ hA.ne' (halphaInj (hscale hA hs) (hscale hA ht) heq)
  have hbetaUnitInj : InjOn betaUnit (Icc 0 1) := by
    intro s hs t ht heq
    exact mul_left_cancel₀ hB.ne' (hbetaInj (hscale hB hs) (hscale hB ht) heq)
  have hunit0 : alphaUnit 0 = betaUnit 0 := by simpa only [alphaUnit, betaUnit, mul_zero] using h0
  have hunit1 : alphaUnit 1 = betaUnit 1 := by simpa only [alphaUnit, betaUnit, mul_one] using hend
  have hunitMeet : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      alphaUnit s = betaUnit t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s hs t ht heq
    rcases hmeet (A * s) (hscale hA hs) (B * t) (hscale hB ht) heq with h | h
    · exact Or.inl ⟨(mul_eq_zero.mp h.1).resolve_left hA.ne',
        (mul_eq_zero.mp h.2).resolve_left hB.ne'⟩
    · exact Or.inr ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
  have hscaleImage (f : ℝ → AnnulusCoordinates) {C : ℝ} (hC : 0 < C) :
      (fun s => f (C * s)) '' Icc (0 : ℝ) 1 = f '' Icc 0 C := by
    apply Subset.antisymm
    · rintro p ⟨s, hs, rfl⟩
      exact ⟨C * s, hscale hC hs, rfl⟩
    · rintro p ⟨s, hs, rfl⟩
      refine ⟨s / C, ⟨div_nonneg hs.1 hC.le, (div_le_one hC).mpr hs.2⟩, ?_⟩
      field_simp
  obtain ⟨loop, hcont, hclosed, hinj, himage⟩ :=
    exists_unit_loop_between_arcs halphaUnit hbetaUnit halphaUnitInj hbetaUnitInj
      hunit0 hunit1 hunitMeet
  refine ⟨loop, hcont, hclosed, hinj, ?_⟩
  exact himage.trans (congrArg₂ (· ∪ ·) (hscaleImage alpha hA) (hscaleImage beta hB))

end PoincareConjecture
