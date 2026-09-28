import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PrefixConfinement
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularLoop
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCrossing
import PoincareConjecture.Proofs.M64.Mathlib.InjectiveDomainClosure





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture






theorem m64Intrinsic_normal_ray_injOn_of_local_prefix_separation
    {e : AnnulusCoordinates → AnnulusCoordinates} (he : ContDiff ℝ ∞ e)
    (hbase : ∀ p, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    {a T h : ℝ} (hT : 0 < T) (hTh : T ≤ h)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a)
      (deriv (fun t => e !₂[a, t]) 0))
    (hinside : ∀ t ∈ Ioo 0 T, 1 < ‖e !₂[a, t]‖ ∧ ‖e !₂[a, t]‖ < 2)
    (hreg : ∀ t ∈ Icc 0 T, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]))
    {I : Set ℝ} (hI : IsOpen I) (haI : a ∈ I)
    (hseparate : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → ∀ A ∈ Ioo 0 h, ∀ B ∈ Ioo 0 h,
      InjOn (fun t => e !₂[p, t]) (Icc 0 A) →
      InjOn (fun t => e !₂[q, t]) (Icc 0 B) →
      (∀ t ∈ Ioc 0 A, 1 < ‖e !₂[p, t]‖ ∧ ‖e !₂[p, t]‖ < 2) →
      (∀ t ∈ Ioc 0 B, 1 < ‖e !₂[q, t]‖ ∧ ‖e !₂[q, t]‖ < 2) →
      e !₂[p, A] ≠ e !₂[q, B]) : InjOn (fun t => e !₂[a, t]) (Icc 0 T) := by
  classical
  have hh : 0 < h := hT.trans_le hTh
  have heta (z : AnnulusCoordinates) : !₂[z 0, z 1] = z := by ext i; fin_cases i <;> rfl
  have hcoord0 : Continuous (fun z : AnnulusCoordinates => z 0) := by fun_prop
  have hcoord1 : Continuous (fun z : AnnulusCoordinates => z 1) := by fun_prop
  have hline : Continuous (fun t : ℝ => (!₂[a, t] : AnnulusCoordinates)) := by fun_prop
  obtain ⟨F0, haF0, _, hF0, _, _⟩ := m64Intrinsic_exists_smooth_polar_inverse
    isOpen_univ (contMDiff_iff_contDiff.mpr he).contMDiffOn (mem_univ _)
    (hreg 0 ⟨le_rfl, hT.le⟩)
  obtain ⟨epsilon, hepsilon, W, hW, haW, hcollar⟩ :=
    m64Intrinsic_exists_signed_normal_collar he hbase hinward F0.open_source haF0
  let d := min epsilon (h / 2)
  have hd : 0 < d := lt_min hepsilon (by positivity)
  have hde : d ≤ epsilon := min_le_left _ _
  have hdh : d < h := (min_le_right _ _).trans_lt (by linarith only [hh])
  let C : Set AnnulusCoordinates := {z | z 0 ∈ W ∩ I ∧ |z 1| < d}
  have hC : IsOpen C := ((hW.inter hI).preimage hcoord0).inter
    (isOpen_lt hcoord1.abs continuous_const)
  have haC : !₂[a, 0] ∈ C := ⟨⟨haW, haI⟩, by
    change |(0 : ℝ)| < d
    simpa only [abs_zero] using hd⟩
  have hCsource : C ⊆ F0.source := by
    intro z hz
    have ht : z 1 ∈ Icc (-epsilon) epsilon := abs_le.mp (hz.2.le.trans hde)
    simpa only [heta] using (hcollar (z 0) hz.1.1 (z 1) ht).1
  let Q : Set AnnulusCoordinates := {z | z 0 ∈ I ∧ 0 < z 1 ∧ z 1 < h ∧
    InjOn (fun t => e !₂[z 0, t]) (Icc 0 (z 1)) ∧
    ∀ t ∈ Ioc 0 (z 1), 1 < ‖e !₂[z 0, t]‖ ∧ ‖e !₂[z 0, t]‖ < 2}
  have hCpositive : ∀ z ∈ C, 0 < z 1 → z ∈ Q := by
    intro z hz hzpos
    have hzd : z 1 < d := by simpa only [abs_of_pos hzpos] using hz.2
    have hsegment (t : ℝ) (ht : t ∈ Icc 0 (z 1)) : !₂[z 0, t] ∈ C :=
      ⟨hz.1, by
        change |t| < d
        simpa only [abs_of_nonneg ht.1] using ht.2.trans_lt hzd⟩
    refine ⟨hz.1.2, hzpos, hzd.trans hdh, ?_, ?_⟩
    · intro s hs t ht heq
      have hst := F0.injOn (hCsource (hsegment s hs)) (hCsource (hsegment t ht))
        (by simpa only [hF0] using heq)
      exact congrArg (fun x : AnnulusCoordinates => x 1) hst
    · intro t ht
      have htc : t ∈ Icc (-epsilon) epsilon :=
        ⟨by linarith only [hepsilon, ht.1], ht.2.trans (hzd.le.trans hde)⟩
      have hc := hcollar (z 0) hz.1.1 t htc
      exact ⟨hc.2.2.2 ht.1, hc.2.1⟩
  have hCnonpositive : ∀ z ∈ C, z 1 ≤ 0 → ‖e z‖ ≤ 1 := by
    intro z hz hzneg
    rcases hzneg.eq_or_lt with hz0 | hzlt
    · rw [← heta z, hz0, hbase, m64Intrinsic_inner_boundary_norm]
    · have ht : z 1 ∈ Icc (-epsilon) epsilon := abs_le.mp (hz.2.le.trans hde)
      have hc := (hcollar (z 0) hz.1.1 (z 1) ht).2.2.1 hzlt
      simpa only [heta] using hc.le
  have hQnorm (z : AnnulusCoordinates) (hz : z ∈ Q) : 1 < ‖e z‖ := by
    simpa only [heta] using (hz.2.2.2.2 (z 1) ⟨hz.2.1, le_rfl⟩).1
  have hQinj : InjOn e Q := by
    intro x hx y hy heq
    have heq' : e !₂[x 0, x 1] = e !₂[y 0, y 1] := by simpa only [heta] using heq
    by_cases hxy : x 0 = y 0
    · have ht : x 1 = y 1 := by
        rcases le_total (x 1) (y 1) with hle | hle
        · rw [hxy] at heq'
          exact hy.2.2.2.1 ⟨hx.2.1.le, hle⟩ ⟨hy.2.1.le, le_rfl⟩ heq'
        · rw [← hxy] at heq'
          exact hx.2.2.2.1 ⟨hx.2.1.le, le_rfl⟩ ⟨hy.2.1.le, hle⟩ heq'
      ext i
      fin_cases i
      · exact hxy
      · exact ht
    · exact (hseparate (x 0) hx.1 (y 0) hy.1 hxy (x 1) ⟨hx.2.1, hx.2.2.1⟩
        (y 1) ⟨hy.2.1, hy.2.2.1⟩ hx.2.2.2.1 hy.2.2.2.1 hx.2.2.2.2 hy.2.2.2.2 heq').elim
  let P := Q ∪ C
  have hPinj : InjOn e P := by
    intro x hx y hy heq
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hQinj hx hy heq
    · by_cases hypos : 0 < y 1
      · exact hQinj hx (hCpositive y hy hypos) heq
      · have hn := hQnorm x hx
        rw [heq] at hn
        exact (not_lt_of_ge (hCnonpositive y hy (le_of_not_gt hypos)) hn).elim
    · by_cases hxpos : 0 < x 1
      · exact hQinj (hCpositive x hx hxpos) hy heq
      · have hn := hQnorm y hy
        rw [← heq] at hn
        exact (not_lt_of_ge (hCnonpositive x hx (le_of_not_gt hxpos)) hn).elim
    · exact F0.injOn (hCsource hx) (hCsource hy) (by simpa only [hF0] using heq)
  by_contra hnot
  have hlocal (t : ℝ) (ht : t ∈ Icc 0 T) :
      ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ InjOn (fun s => e !₂[a, s]) J := by
    obtain ⟨F, htF, _, hF, _, _⟩ := m64Intrinsic_exists_smooth_polar_inverse
      isOpen_univ (contMDiff_iff_contDiff.mpr he).contMDiffOn (mem_univ _) (hreg t ht)
    refine ⟨(fun s => !₂[a, s]) ⁻¹' F.source, F.open_source.preimage hline, htF, ?_⟩
    intro s hs v hv heq
    exact congrArg (fun z : AnnulusCoordinates => z 1)
      (F.injOn hs hv (by simpa only [hF] using heq))
  obtain ⟨s, t, hs, hst, htT, hreturn, hprefix⟩ :=
    m64Intrinsic_exists_first_return_interval (he.continuous.comp hline) hlocal hnot
  change e !₂[a, s] = e !₂[a, t] at hreturn
  change InjOn (fun v => e !₂[a, v]) (Ico 0 t) at hprefix
  have htpos : 0 < t := hs.trans_lt hst
  have hprefixP : (fun v => !₂[a, v]) '' Ioo 0 t ⊆ P := by
    rintro _ ⟨v, hv, rfl⟩
    refine Or.inl ⟨haI, hv.1, hv.2.trans_le (htT.trans hTh), ?_, ?_⟩
    · exact hprefix.mono (show Icc 0 v ⊆ Ico 0 t from
        fun u hu => ⟨hu.1, hu.2.trans_lt hv.2⟩)
    · intro u hu
      exact hinside u ⟨hu.1, (hu.2.trans_lt hv.2).trans_le htT⟩
  have htClosure : !₂[a, t] ∈ closure P := by
    apply (closure_mono hprefixP)
    apply image_closure_subset_closure_image hline
    refine ⟨t, ?_, rfl⟩
    rw [closure_Ioo htpos.ne]
    exact ⟨htpos.le, le_rfl⟩
  have hsource : ∃ O : Set AnnulusCoordinates, IsOpen O ∧ !₂[a, s] ∈ O ∧ O ⊆ P := by
    rcases hs.eq_or_lt with hs0 | hspos
    · have hs' : s = 0 := hs0.symm
      exact ⟨C, hC, hs' ▸ haC, subset_union_right⟩
    · obtain ⟨v, hsv, hvt⟩ := exists_between hst
      have hvpos : 0 < v := hspos.trans hsv
      obtain ⟨W', hW', haW', hstable⟩ := m64Intrinsic_exists_stable_annular_prefix
        he hbase hvpos hinward
        (fun u hu => hinside u ⟨hu.1, (hu.2.trans_lt hvt).trans_le htT⟩)
        (hprefix.mono (show Icc 0 v ⊆ Ico 0 t from
          fun u hu => ⟨hu.1, hu.2.trans_lt hvt⟩))
        (fun u hu => hreg u ⟨hu.1, (hu.2.trans hvt.le).trans htT⟩)
      let O : Set AnnulusCoordinates := {z | z 0 ∈ W' ∩ I ∧ z 1 ∈ Ioo 0 v}
      have hO : IsOpen O := ((hW'.inter hI).preimage hcoord0).inter
        (isOpen_Ioo.preimage hcoord1)
      refine ⟨O, hO, ⟨⟨haW', haI⟩, hspos, hsv⟩, ?_⟩
      intro z hz
      refine Or.inl ⟨hz.1.2, hz.2.1, (hz.2.2.trans hvt).trans_le (htT.trans hTh), ?_, ?_⟩
      · exact (hstable (z 0) hz.1.1).1.mono (Icc_subset_Icc_right hz.2.2.le)
      · intro u hu
        exact (hstable (z 0) hz.1.1).2 u ⟨hu.1, hu.2.trans hz.2.2.le⟩
  obtain ⟨O, hO, hsO, hOP⟩ := hsource
  obtain ⟨F, hsF, hFO, hF, _, _⟩ := m64Intrinsic_exists_smooth_polar_inverse hO
    (contMDiff_iff_contDiff.mpr he).contMDiffOn hsO (hreg s ⟨hs, hst.le.trans htT⟩)
  have htarget : e !₂[a, t] ∈ F.target := by
    rw [← hreturn]
    simpa only [hF] using F.map_source hsF
  have heq := m64_eq_local_inverse_of_injOn_closure he.continuous.continuousAt hPinj
    htClosure F (fun z _ => congrFun hF z) (hFO.trans hOP) htarget
  have hback : F.symm (e !₂[a, t]) = !₂[a, s] := by
    rw [← hreturn, ← hF]
    exact F.left_inv hsF
  rw [hback] at heq
  have htime := congrArg (fun z : AnnulusCoordinates => z 1) heq
  exact hst.ne htime.symm

end PoincareConjecture
