import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CrossRayRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AnnularBigonRegion

















noncomputable section
set_option autoImplicit false

open Set Function Metric
open scoped Topology

namespace PoincareConjecture





theorem m64Intrinsic_exists_crossing_annular_region
    {alpha beta base : ℝ → AnnulusCoordinates} {A B a b : ℝ}
    (hab : a < b) (hperiod : b - a < rampPeriod)
    (ha : Continuous alpha) (hb : Continuous beta)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b)
    (hαinside : ∀ t ∈ Ioc 0 A, 1 < ‖alpha t‖ ∧ ‖alpha t‖ < 2)
    (hβinside : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖ ∧ ‖beta t‖ < 2)
    (hstart : base 0 = alpha 0) (hend : base 1 = beta 0)
    (hca : ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 A,
      base x = alpha t → x = 0 ∧ t = 0)
    (hcb : ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 B,
      base x = beta t → x = 1 ∧ t = 0)
    (hmeet : ∃ s ∈ Icc 0 A, ∃ t ∈ Icc 0 B, alpha s = beta t) :
    ∃ gamma : ℝ → AnnulusCoordinates, ∃ U V : Set AnnulusCoordinates,
      Continuous gamma ∧ InjOn gamma (Icc 0 1) ∧
      gamma 0 = intrinsicAnnulusBoundary 1 a ∧
      gamma 1 = intrinsicAnnulusBoundary 1 b ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 1 < ‖gamma x‖ ∧ ‖gamma x‖ < 2) ∧
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (frontier U)ᶜ ∧ frontier V = frontier U ∧
      IsCompact (closure U) ∧ closure U ⊆ standardAnnulusDomain ∧
      (frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
          gamma '' Icc 0 1 ∨
        frontier U = intrinsicAnnulusBoundary 1 '' Icc b (a + rampPeriod) ∪
          gamma '' Icc 0 1) := by
  have ha0cross : alpha 0 ∉ beta '' Icc 0 B := by
    rintro ⟨t, ht, heq⟩
    have h := (hcb 0 (by norm_num) t ht (hstart.trans heq.symm)).1
    norm_num at h
  have hb0cross : beta 0 ∉ alpha '' Icc 0 A := by
    rintro ⟨s, hs, heq⟩
    have h := (hca 1 (by norm_num) s hs (hend.trans heq.symm)).1
    norm_num at h
  obtain ⟨s, t, hs, hsA, ht, htB, hst, hfirst⟩ :=
    m64Intrinsic_exists_first_crossing ha hb ha0cross hb0cross hmeet
  let f : ℝ → AnnulusCoordinates := fun x => alpha (s * x)
  let g : ℝ → AnnulusCoordinates := fun x => beta (t * (1 - x))
  have hsparam (x : ℝ) (hx : x ∈ Icc 0 1) : s * x ∈ Icc 0 s :=
    ⟨mul_nonneg hs.le hx.1, by nlinarith [hx.2]⟩
  have htparam (x : ℝ) (hx : x ∈ Icc 0 1) : t * (1 - x) ∈ Icc 0 t :=
    ⟨by nlinarith [hx.2], by nlinarith [hx.1]⟩
  have hf : ContinuousOn f (Icc 0 1) :=
    (ha.comp (continuous_const.mul continuous_id)).continuousOn
  have hg : ContinuousOn g (Icc 0 1) :=
    (hb.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have hfi : InjOn f (Icc 0 1) := by
    intro x hx y hy hxy
    have h := hai (x₁ := s * x) (x₂ := s * y)
      ⟨(hsparam x hx).1, (hsparam x hx).2.trans hsA⟩
      ⟨(hsparam y hy).1, (hsparam y hy).2.trans hsA⟩ hxy
    exact mul_left_cancel₀ hs.ne' h
  have hgi : InjOn g (Icc 0 1) := by
    intro x hx y hy hxy
    have h := hbi (x₁ := t * (1 - x)) (x₂ := t * (1 - y))
      ⟨(htparam x hx).1, (htparam x hx).2.trans htB⟩
      ⟨(htparam y hy).1, (htparam y hy).2.trans htB⟩ hxy
    nlinarith
  have hfg : f 1 = g 0 := by simpa only [f, g, mul_one, sub_zero] using hst
  have hfgmeet : ∀ x ∈ Icc 0 1, ∀ y ∈ Icc 0 1,
      f x = g y → x = 1 ∧ y = 0 := by
    intro x hx y hy hxy
    have h := hfirst (s * x) (hsparam x hx) (t * (1 - y)) (htparam y hy) hxy
    constructor <;> nlinarith [h.1, h.2]
  obtain ⟨q, hq, hqi, hq0, hq1, hqimage⟩ :=
    m64Intrinsic_exists_embedded_join hf hg hfi hgi hfg hfgmeet
  have hq0' : q 0 = intrinsicAnnulusBoundary 1 a := by
    calc q 0 = f 0 := hq0
      _ = alpha 0 := by simp [f]
      _ = intrinsicAnnulusBoundary 1 a := ha0
  have hq1' : q 1 = intrinsicAnnulusBoundary 1 b := by
    calc q 1 = g 1 := hq1
      _ = beta 0 := by simp [g]
      _ = intrinsicAnnulusBoundary 1 b := hb0
  let qpath : Path (q 0) (q 1) :=
    { toContinuousMap :=
        ⟨fun x : Set.Icc (0 : ℝ) 1 => q x, hq.domRestrict⟩
      source' := rfl
      target' := rfl }
  let gamma : ℝ → AnnulusCoordinates := qpath.extend
  have hgamma : Continuous gamma := qpath.continuous_extend
  have hgamma_i : InjOn gamma (Icc 0 1) := by
    intro x hx y hy hxy
    have hxy' : q x = q y := by
      have hxy0 : qpath.extend x = qpath.extend y := by
        simpa only [gamma] using hxy
      rw [Path.extend_apply qpath hx,
        Path.extend_apply qpath hy] at hxy0
      exact hxy0
    exact hqi hx hy hxy'
  have hgamma0 : gamma 0 = intrinsicAnnulusBoundary 1 a := by
    simpa only [gamma, Path.extend_zero] using hq0'
  have hgamma1 : gamma 1 = intrinsicAnnulusBoundary 1 b := by
    simpa only [gamma, Path.extend_one] using hq1'
  have hgammaInside : ∀ x ∈ Ioo (0 : ℝ) 1,
      1 < ‖gamma x‖ ∧ ‖gamma x‖ < 2 := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hmem : gamma x ∈ f '' Icc 0 1 ∪ g '' Icc 0 1 := by
      rw [← hqimage]
      refine ⟨x, hxIcc, ?_⟩
      change q x = qpath.extend x
      exact (Path.extend_apply qpath hxIcc).symm
    rcases hmem with ⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩
    · have hzpos : 0 < z := by
        by_contra hzpos
        have hz0 : z = 0 := le_antisymm (le_of_not_gt hzpos) hz.1
        have hf0 : f 0 = gamma 0 := by
          calc f 0 = alpha 0 := by simp [f]
            _ = intrinsicAnnulusBoundary 1 a := ha0
            _ = gamma 0 := hgamma0.symm
        have heq : gamma x = gamma 0 := by
          calc gamma x = f z := hzx.symm
            _ = f 0 := by rw [hz0]
            _ = gamma 0 := hf0
        have hxzero := hgamma_i (x₁ := x) (x₂ := (0 : ℝ)) hxIcc
          ⟨le_rfl, zero_le_one⟩ heq
        exact (ne_of_gt hx.1) hxzero
      have hparam : s * z ∈ Ioc 0 A :=
        ⟨mul_pos hs hzpos, (hsparam z hz).2.trans hsA⟩
      rw [← hzx]
      exact hαinside (s * z) hparam
    · have hzlt : z < 1 := by
        by_contra hzlt
        have hz1 : z = 1 := le_antisymm hz.2 (le_of_not_gt hzlt)
        have hg1 : g 1 = gamma 1 := by
          calc g 1 = beta 0 := by simp [g]
            _ = intrinsicAnnulusBoundary 1 b := hb0
            _ = gamma 1 := hgamma1.symm
        have heq : gamma x = gamma 1 := by
          calc gamma x = g z := hzx.symm
            _ = g 1 := by rw [hz1]
            _ = gamma 1 := hg1
        have hxone := hgamma_i (x₁ := x) (x₂ := (1 : ℝ)) hxIcc
          ⟨zero_le_one, le_rfl⟩ heq
        exact (ne_of_lt hx.2) hxone
      have hparam : t * (1 - z) ∈ Ioc 0 B :=
        ⟨mul_pos ht (sub_pos.mpr hzlt), (htparam z hz).2.trans htB⟩
      rw [← hzx]
      exact hβinside (t * (1 - z)) hparam
  obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd, hcU, hfV, hk, hsub, hfront⟩ :=
    m64Intrinsic_embedded_inner_return_annular_region hab hperiod (by norm_num)
      hgamma hgamma_i hgamma0 hgamma1 hgammaInside
  exact ⟨gamma, U, V, hgamma, hgamma_i, hgamma0, hgamma1, hgammaInside,
    hU, hV, hpU, hpV, hbU, hbV, hd, hcU, hfV, hk, hsub, hfront⟩

end PoincareConjecture
