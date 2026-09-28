import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopCapContacts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_loop_cap_tip_unique
    {gamma : ℝ → AnnulusCoordinates} {T r : ℝ} (hr : 0 < r) (hrT : r < T)
    (hinj : InjOn gamma (Ico 0 T))
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (hbase : H 0 = gamma 0)
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hfirst : ∀ i, ∀ s ∈ Icc (0 : ℝ) r, F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ i, ∀ s ∈ Icc (0 : ℝ) r, F i (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (positive terminal : Bool) :
    ∀ i : Bool × Bool, (if positive then i = (true, true) else i ≠ (true, true)) →
      gamma (if terminal then T - r else r) ∈
        F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} →
      i = if terminal then (positive, true) else (true, positive) := by
  let C (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  let p := if terminal then T - r else r
  let q := H.symm (gamma p)
  have hcoordinates (i : Bool × Bool) (hz : gamma p ∈ C i) :
      (if i.1 then 0 ≤ q.1 else q.1 ≤ 0) ∧
        (if i.2 then 0 ≤ q.2 else q.2 ≤ 0) := by
    obtain ⟨_, ⟨hs, u, hu, rfl⟩, heq⟩ := hsector i hz
    have hq : q = sectorParameterEquiv 0 i u := by
      change H.symm (gamma p) = _
      rw [← heq, H.left_inv hs]
    rw [hq]
    rcases i with ⟨i, j⟩
    cases i <;> cases j <;> simp [sectorParameterEquiv_apply, hu.1, hu.2]
  have htip : gamma p ∈ C (true, true) := by
    cases terminal
    · refine ⟨(r, 0), ⟨hr.le, le_rfl, by simp⟩, ?_⟩
      simpa [p, sectorParameterEquiv_apply, haxis] using hfirst (true, true) r ⟨hr.le, le_rfl⟩
    · refine ⟨(0, r), ⟨le_rfl, hr.le, by simp⟩, ?_⟩
      simpa [p, sectorParameterEquiv_apply, haxis'] using hsecond (true, true) r ⟨hr.le, le_rfl⟩
  have hqpos : 0 ≤ q.1 ∧ 0 ≤ q.2 := hcoordinates (true, true) htip
  have hptarget : gamma p ∈ H.target := by
    obtain ⟨u, hu, heq⟩ := hsector (true, true) htip
    exact heq ▸ H.map_source hu.1
  have hp : p ∈ Ioo (0 : ℝ) T := by
    cases terminal
    · exact ⟨hr, hrT⟩
    · exact ⟨sub_pos.mpr hrT, sub_lt_self T hr⟩
  have hqne : q ≠ 0 := by
    intro hzero
    have heq : gamma p = gamma 0 := by
      rw [← H.right_inv hptarget]
      change H q = gamma 0
      rw [hzero, hbase]
    have hpzero := hinj ⟨hp.1.le, hp.2⟩ ⟨le_rfl, hp.1.trans hp.2⟩ heq
    exact hp.1.ne' hpzero
  intro i hi hmember
  cases positive
  · have hci := hcoordinates i hmember
    cases terminal
    · have hother : gamma p ∈ C (true, false) := by
        refine ⟨(r, 0), ⟨hr.le, le_rfl, by simp⟩, ?_⟩
        simpa [p, sectorParameterEquiv_apply, haxis] using hfirst (true, false) r ⟨hr.le, le_rfl⟩
      have hq2 : q.2 = 0 := le_antisymm (hcoordinates (true, false) hother).2 hqpos.2
      have hq1 : 0 < q.1 := lt_of_le_of_ne hqpos.1 (fun heq => hqne (Prod.ext heq.symm hq2))
      rcases i with ⟨i, j⟩
      cases i <;> cases j <;> simp_all <;> linarith
    · have hother : gamma p ∈ C (false, true) := by
        refine ⟨(0, r), ⟨le_rfl, hr.le, by simp⟩, ?_⟩
        simpa [p, sectorParameterEquiv_apply, haxis'] using hsecond (false, true) r ⟨hr.le, le_rfl⟩
      have hq1 : q.1 = 0 := le_antisymm (hcoordinates (false, true) hother).1 hqpos.1
      have hq2 : 0 < q.2 := lt_of_le_of_ne hqpos.2 (fun heq => hqne (Prod.ext hq1 heq.symm))
      rcases i with ⟨i, j⟩
      cases i <;> cases j <;> simp_all <;> linarith
  · cases terminal <;> exact hi

end PoincareConjecture
