import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanRegion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_regular_curve_locally_injective
    {gamma : ℝ → AnnulusCoordinates} {s : ℝ}
    (hg : ContDiffAt ℝ ∞ gamma s) (hregular : deriv gamma s ≠ 0) :
    ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ InjOn gamma U := by
  have hcoord : ∃ i : Fin 2, deriv gamma s i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hregular
    ext i
    exact hn i
  obtain ⟨i, hi⟩ := hcoord
  let f : ℝ → ℝ := fun t => gamma t i
  have hproj : ContDiff ℝ ∞ (fun z : AnnulusCoordinates => z i) := by fun_prop
  have hf : ContDiffAt ℝ ∞ f s := hproj.contDiffAt.comp s hg
  have hdf : HasDerivAt f (deriv gamma s i) s :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (gamma s) i).comp_hasDerivAt s
      (hg.differentiableAt (by simp)).hasDerivAt
  have hstrict := hf.hasStrictDerivAt' hdf (by simp)
  have hinv := hstrict.eventually_left_inverse hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hinv
  refine ⟨ball s r, isOpen_ball, mem_ball_self hr, ?_⟩
  intro x hx y hy heq
  calc
    x = hstrict.localInverse f _ s hi (f x) := (hball hx).symm
    _ = hstrict.localInverse f _ s hi (f y) := by
      rw [show f x = f y from congrArg (fun z => z i) heq]
    _ = y := hball hy

theorem m64Intrinsic_regular_return_separation
    {gamma : ℝ → AnnulusCoordinates} {a b : ℝ}
    (hlocal : ∀ s ∈ Icc a b, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ InjOn gamma U) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      s < t → gamma s = gamma t → epsilon ≤ t - s := by
  choose U hU hsU hi using hlocal
  have hcover : Icc a b ⊆ ⋃ s : Icc a b, U s.val s.property := by
    intro s hs
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hsU s hs⟩
  obtain ⟨epsilon, hepsilon, hsmall⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun s : Icc a b => hU s.val s.property) hcover
  refine ⟨epsilon, hepsilon, ?_⟩
  intro s hs t _ hst heq
  obtain ⟨p, hp⟩ := hsmall s hs
  by_contra hn
  have htball : t ∈ ball s epsilon := by
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hst)]
    exact lt_of_not_ge hn
  exact hst.ne ((hi p.val p.property) (hp (mem_ball_self hepsilon)) (hp htball) heq)

theorem m64Intrinsic_exists_first_return_interval
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {a b : ℝ}
    (hlocal : ∀ s ∈ Icc a b, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ InjOn gamma U)
    (hnot : ¬ InjOn gamma (Icc a b)) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧ gamma s = gamma t ∧ InjOn gamma (Ico a t) := by
  obtain ⟨epsilon, hepsilon, hsep⟩ := m64Intrinsic_regular_return_separation hlocal
  let C : Set (ℝ × ℝ) := (Icc a b ×ˢ Icc a b) ∩
    {p | epsilon ≤ p.2 - p.1 ∧ gamma p.1 = gamma p.2}
  have hC : IsCompact C := (isCompact_Icc.prod isCompact_Icc).inter_right
    ((isClosed_le continuous_const (continuous_snd.sub continuous_fst)).inter
      (isClosed_eq (hg.comp continuous_fst) (hg.comp continuous_snd)))
  have hpair : ∃ s ∈ Icc a b, ∃ t ∈ Icc a b, s < t ∧ gamma s = gamma t := by
    simp only [InjOn] at hnot
    push Not at hnot
    obtain ⟨s, hs, t, ht, heq, hne⟩ := hnot
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨s, hs, t, ht, hlt, heq⟩
    · exact ⟨t, ht, s, hs, hlt, heq.symm⟩
  obtain ⟨s, hs, t, ht, hst, heq⟩ := hpair
  have hCne : C.Nonempty := ⟨(s, t), ⟨⟨hs, ht⟩, hsep s hs t ht hst heq, heq⟩⟩
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hCne continuous_snd.continuousOn
  have hplt : p.1 < p.2 := by linarith [hp.2.1]
  refine ⟨p.1, p.2, hp.1.1.1, hplt, hp.1.2.2, hp.2.2, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  wlog hlt : x < y generalizing x y
  · exact this (x := y) (y := x) hy hx hxy.symm (Ne.symm hne)
      (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne))
  have hxI : x ∈ Icc a b := ⟨hx.1, hx.2.le.trans hp.1.2.2⟩
  have hyI : y ∈ Icc a b := ⟨hy.1, hy.2.le.trans hp.1.2.2⟩
  have hxyC : (x, y) ∈ C := ⟨⟨hxI, hyI⟩, hsep x hxI y hyI hlt hxy, hxy⟩
  have hlength := hmin hxyC
  change p.2 ≤ y at hlength
  exact not_le_of_gt hy.2 hlength

theorem m64Intrinsic_exists_simple_return_interval
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {a b : ℝ}
    (hlocal : ∀ s ∈ Icc a b, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ InjOn gamma U)
    (hnot : ¬ InjOn gamma (Icc a b)) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧ gamma s = gamma t ∧ InjOn gamma (Ico s t) := by
  obtain ⟨s, t, has, hst, htb, heq, hinj⟩ :=
    m64Intrinsic_exists_first_return_interval hg hlocal hnot
  exact ⟨s, t, has, hst, htb, heq, hinj.mono (Ico_subset_Ico_left has)⟩

theorem m64Intrinsic_exists_simple_regular_loop
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {a b : ℝ}
    (hregular : ∀ s ∈ Icc a b, deriv gamma s ≠ 0)
    (hnot : ¬ InjOn gamma (Icc a b)) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧ gamma s = gamma t ∧ InjOn gamma (Ico s t) :=
  m64Intrinsic_exists_simple_return_interval hg.continuous
    (fun s hs => m64Intrinsic_regular_curve_locally_injective hg.contDiffAt (hregular s hs)) hnot

end PoincareConjecture
