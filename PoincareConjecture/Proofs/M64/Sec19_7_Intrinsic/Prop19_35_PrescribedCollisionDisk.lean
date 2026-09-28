import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCrossing
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedJordanRegions
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryParameters

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Metric
open scoped Topology ContDiff

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem m64Intrinsic_exists_fixed_crossing_ray_region
    {alpha beta base : ℝ → AnnulusCoordinates} {A B s t : ℝ}
    (ha : Continuous alpha) (hb : Continuous beta)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hc : ContinuousOn base (Icc 0 1)) (hci : InjOn base (Icc 0 1))
    (hstart : base 0 = alpha 0) (hend : base 1 = beta 0)
    (hca : ∀ x ∈ Icc 0 1, ∀ q ∈ Icc 0 A,
      base x = alpha q → x = 0 ∧ q = 0)
    (hcb : ∀ x ∈ Icc 0 1, ∀ q ∈ Icc 0 B,
      base x = beta q → x = 1 ∧ q = 0)
    (hs : 0 < s) (hsA : s ≤ A) (ht : 0 < t) (htB : t ≤ B)
    (hst : alpha s = beta t)
    (hfirst : ∀ x ∈ Icc 0 s, ∀ y ∈ Icc 0 t,
      alpha x = beta y → x = s ∧ y = t) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (base '' Icc 0 1 ∪ (alpha '' Icc 0 s ∪ beta '' Icc 0 t))ᶜ ∧
      frontier U = base '' Icc 0 1 ∪ (alpha '' Icc 0 s ∪ beta '' Icc 0 t) ∧
      frontier V = base '' Icc 0 1 ∪ (alpha '' Icc 0 s ∪ beta '' Icc 0 t) ∧
      IsCompact (closure U) := by
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
    have h := hai ⟨(hsparam x hx).1, (hsparam x hx).2.trans hsA⟩
      ⟨(hsparam y hy).1, (hsparam y hy).2.trans hsA⟩ hxy
    exact mul_left_cancel₀ hs.ne' h
  have hgi : InjOn g (Icc 0 1) := by
    intro x hx y hy hxy
    have h := hbi ⟨(htparam x hx).1, (htparam x hx).2.trans htB⟩
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
  have hfimage : f '' Icc 0 1 = alpha '' Icc 0 s := by
    change (alpha ∘ fun x => s * x) '' Icc 0 1 = _
    rw [image_comp, image_mul_left_Icc' hs]
    simp only [mul_zero, mul_one]
  have hgimage : g '' Icc 0 1 = beta '' Icc 0 t := by
    change (beta ∘ (fun x => t * x) ∘ (fun x => 1 - x)) '' Icc 0 1 = _
    rw [image_comp, image_comp, image_const_sub_Icc]
    norm_num only [sub_self, sub_zero]
    rw [image_mul_left_Icc' ht]
    simp only [mul_zero, mul_one]
  have hq0' : q 0 = alpha 0 := by simpa only [f, mul_zero] using hq0
  have hq1' : q 1 = beta 0 := by simpa only [g, sub_self, mul_zero] using hq1
  have hbaseq : ∀ x ∈ Icc 0 1, ∀ y ∈ Icc 0 1,
      base x = q y → (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
    intro x hx y hy hxy
    have hyimage : q y ∈ f '' Icc 0 1 ∪ g '' Icc 0 1 :=
      hqimage ▸ mem_image_of_mem q hy
    rcases hyimage with ⟨z, hz, hzq⟩ | ⟨z, hz, hzq⟩
    · have h := hca x hx (s * z)
        ⟨(hsparam z hz).1, (hsparam z hz).2.trans hsA⟩ (hxy.trans hzq.symm)
      refine Or.inl ⟨h.1, hqi hy (by norm_num) ?_⟩
      rw [← hxy, h.1, hq0', hstart]
    · have h := hcb x hx (t * (1 - z))
        ⟨(htparam z hz).1, (htparam z hz).2.trans htB⟩ (hxy.trans hzq.symm)
      refine Or.inr ⟨h.1, hqi hy (by norm_num) ?_⟩
      rw [← hxy, h.1, hq1', hend]
  obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj, hcover, hfU, hfV, hcompact⟩ :=
    m64Intrinsic_exists_region_between_arcs hc hq hci hqi
      (hstart.trans hq0'.symm) (hend.trans hq1'.symm) hbaseq
  rw [hqimage, hfimage, hgimage] at hcover hfU hfV
  exact ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj, hcover, hfU, hfV, hcompact⟩

theorem m64Intrinsic_exists_prescribed_collision_disk
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u)
    (hboundary : ∀ x : ℝ, u (x, 0) = intrinsicAnnulusBoundary 1 x)
    {a b A B : ℝ} (hab : a < b) (hperiod : b - a < rampPeriod)
    (hai : InjOn (fun s : ℝ => u (a, s)) (Icc (0 : ℝ) A))
    (hbi : InjOn (fun t : ℝ => u (b, t)) (Icc (0 : ℝ) B))
    (haInterior : ∀ s ∈ Ioc (0 : ℝ) A,
      1 < ‖u (a, s)‖ ∧ ‖u (a, s)‖ ≤ 2)
    (hbInterior : ∀ t ∈ Ioc (0 : ℝ) B,
      1 < ‖u (b, t)‖ ∧ ‖u (b, t)‖ ≤ 2)
    (hmeet : ∃ s ∈ Icc (0 : ℝ) A, ∃ t ∈ Icc (0 : ℝ) B,
      u (a, s) = u (b, t)) :
    ∃ s t, ∃ U V : Set AnnulusCoordinates,
      0 < s ∧ s ≤ A ∧ 0 < t ∧ t ≤ B ∧ u (a, s) = u (b, t) ∧
      (∀ x ∈ Icc (0 : ℝ) s, ∀ y ∈ Icc (0 : ℝ) t,
        u (a, x) = u (b, y) → x = s ∧ y = t) ∧
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      Disjoint U V ∧ U ∪ V = (frontier U)ᶜ ∧
      frontier V = frontier U ∧ IsCompact (closure U) ∧
      closure U ⊆ standardAnnulusDomain ∧
      (frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
          ((fun s => u (a, s)) '' Icc 0 s ∪
            (fun t => u (b, t)) '' Icc 0 t) ∨
        frontier U = intrinsicAnnulusBoundary 1 '' Icc b (a + rampPeriod) ∪
          ((fun t => u (b, t)) '' Icc 0 t ∪
            (fun s => u (a, s)) '' Icc 0 s)) := by
  let alpha : ℝ → AnnulusCoordinates := fun s => u (a, s)
  let beta : ℝ → AnnulusCoordinates := fun t => u (b, t)
  have hlineA : ContDiff ℝ ∞ (fun s : ℝ => (a, s)) := by fun_prop
  have hlineB : ContDiff ℝ ∞ (fun t : ℝ => (b, t)) := by fun_prop
  have halpha : Continuous alpha := (hu.comp hlineA).continuous
  have hbeta : Continuous beta := (hu.comp hlineB).continuous
  have ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a := hboundary a
  have hb0 : beta 0 = intrinsicAnnulusBoundary 1 b := hboundary b
  have hshort : ∃ s ∈ Icc (0 : ℝ) A, ∃ t ∈ Icc (0 : ℝ) B,
      alpha s = beta t := by simpa only [alpha, beta] using hmeet
  let base₁ : ℝ → AnnulusCoordinates :=
    fun x => intrinsicAnnulusBoundary 1 ((b - a) * x + a)
  have hparam₁ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (b - a) * x + a ∈ Icc a b :=
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  have hbase₁ : ContinuousOn base₁ (Icc (0 : ℝ) 1) :=
    ((m64Intrinsic_contDiff_boundary 1).continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousOn
  have hbase₁i : InjOn base₁ (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have h := m64Intrinsic_boundary_injOn_short_arc hperiod
      (hparam₁ x hx) (hparam₁ y hy) hxy
    nlinarith
  have hstart₁ : base₁ 0 = alpha 0 := by
    simpa only [base₁, mul_zero, zero_add] using ha0.symm
  have hend₁ : base₁ 1 = beta 0 := by
    simpa only [base₁, mul_one, sub_add_cancel] using hb0.symm
  have hca₁ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) A,
      base₁ x = alpha q → x = 0 ∧ q = 0 := by
    intro x hx q hq heq
    have hq0 : q = 0 := by
      by_contra hne
      have hnorm := haInterior q
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hne), hq.2⟩
      have hnorm' : 1 < ‖alpha q‖ ∧ ‖alpha q‖ ≤ 2 := by
        simpa only [alpha] using hnorm
      rw [← heq] at hnorm'
      exact (lt_irrefl (1 : ℝ))
        (by simpa only [base₁, m64Intrinsic_inner_boundary_norm] using hnorm'.1)
    refine ⟨hbase₁i hx (by norm_num) ?_, hq0⟩
    rw [heq, hq0, hstart₁]
  have hcb₁ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) B,
      base₁ x = beta q → x = 1 ∧ q = 0 := by
    intro x hx q hq heq
    have hq0 : q = 0 := by
      by_contra hne
      have hnorm := hbInterior q
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hne), hq.2⟩
      have hnorm' : 1 < ‖beta q‖ ∧ ‖beta q‖ ≤ 2 := by
        simpa only [beta] using hnorm
      rw [← heq] at hnorm'
      exact (lt_irrefl (1 : ℝ))
        (by simpa only [base₁, m64Intrinsic_inner_boundary_norm] using hnorm'.1)
    refine ⟨hbase₁i hx (by norm_num) ?_, hq0⟩
    rw [heq, hq0, hend₁]
  have ha0not : alpha 0 ∉ beta '' Icc (0 : ℝ) B := by
    rintro ⟨q, hq, heq⟩
    have h := (hcb₁ 0 (by norm_num) q hq (hstart₁.trans heq.symm)).1
    norm_num at h
  have hb0not : beta 0 ∉ alpha '' Icc (0 : ℝ) A := by
    rintro ⟨q, hq, heq⟩
    have h := (hca₁ 1 (by norm_num) q hq (hend₁.trans heq.symm)).1
    norm_num at h
  obtain ⟨s, t, hs, hsA, ht, htB, hst, hfirst⟩ :=
    m64Intrinsic_exists_first_crossing halpha hbeta ha0not hb0not hshort
  obtain ⟨U₁, V₁, hU₁, hV₁, hpU₁, hpV₁, hbU₁, hbV₁, hd₁, hc₁,
      hfU₁, hfV₁, hcompact₁⟩ :=
    m64Intrinsic_exists_fixed_crossing_ray_region halpha hbeta hai hbi
      hbase₁ hbase₁i hstart₁ hend₁ hca₁ hcb₁ hs hsA ht htB hst hfirst
  let alpha₂ : ℝ → AnnulusCoordinates := beta
  let beta₂ : ℝ → AnnulusCoordinates := alpha
  let base₂ : ℝ → AnnulusCoordinates :=
    fun x => intrinsicAnnulusBoundary 1 ((a + rampPeriod - b) * x + b)
  have hab₂ : b < a + rampPeriod := by linarith
  have hperiod₂ : a + rampPeriod - b < rampPeriod := by linarith
  have hparam₂ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (a + rampPeriod - b) * x + b ∈ Icc b (a + rampPeriod) :=
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  have hbase₂ : ContinuousOn base₂ (Icc (0 : ℝ) 1) :=
    ((m64Intrinsic_contDiff_boundary 1).continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousOn
  have hbase₂i : InjOn base₂ (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have h := m64Intrinsic_boundary_injOn_short_arc hperiod₂
      (hparam₂ x hx) (hparam₂ y hy) hxy
    nlinarith
  have hstart₂ : base₂ 0 = alpha₂ 0 := by
    simpa only [base₂, alpha₂, mul_zero, zero_add] using hb0.symm
  have hend₂ : base₂ 1 = beta₂ 0 := by
    rw [show base₂ 1 = intrinsicAnnulusBoundary 1 (a + rampPeriod) by
      simp [base₂], m64Intrinsic_boundary_periodic]
    exact ha0.symm
  have hca₂ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) B,
      base₂ x = alpha₂ q → x = 0 ∧ q = 0 := by
    intro x hx q hq heq
    have hq0 : q = 0 := by
      by_contra hne
      have hnorm := hbInterior q
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hne), hq.2⟩
      have hnorm' : 1 < ‖alpha₂ q‖ ∧ ‖alpha₂ q‖ ≤ 2 := by
        simpa only [alpha₂] using hnorm
      rw [← heq] at hnorm'
      exact (lt_irrefl (1 : ℝ))
        (by simpa only [base₂, m64Intrinsic_inner_boundary_norm] using hnorm'.1)
    refine ⟨hbase₂i hx (by norm_num) ?_, hq0⟩
    rw [heq, hq0, hstart₂]
  have hcb₂ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) A,
      base₂ x = beta₂ q → x = 1 ∧ q = 0 := by
    intro x hx q hq heq
    have hq0 : q = 0 := by
      by_contra hne
      have hnorm := haInterior q
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hne), hq.2⟩
      have hnorm' : 1 < ‖beta₂ q‖ ∧ ‖beta₂ q‖ ≤ 2 := by
        simpa only [beta₂] using hnorm
      rw [← heq] at hnorm'
      exact (lt_irrefl (1 : ℝ))
        (by simpa only [base₂, m64Intrinsic_inner_boundary_norm] using hnorm'.1)
    refine ⟨hbase₂i hx (by norm_num) ?_, hq0⟩
    rw [heq, hq0, hend₂]
  have hfirst₂ : ∀ x ∈ Icc (0 : ℝ) t, ∀ y ∈ Icc (0 : ℝ) s,
      alpha₂ x = beta₂ y → x = t ∧ y = s := by
    intro x hx y hy hxy
    have h := hfirst y hy x hx hxy.symm
    exact ⟨h.2, h.1⟩
  obtain ⟨U₂, V₂, hU₂, hV₂, hpU₂, hpV₂, hbU₂, hbV₂, hd₂, hc₂,
      hfU₂, hfV₂, hcompact₂⟩ :=
    m64Intrinsic_exists_fixed_crossing_ray_region hbeta halpha hbi hai
      hbase₂ hbase₂i hstart₂ hend₂ hca₂ hcb₂ ht htB hs hsA hst.symm hfirst₂
  have hbase₁image : base₁ '' Icc (0 : ℝ) 1 =
      intrinsicAnnulusBoundary 1 '' Icc a b := by
    change (intrinsicAnnulusBoundary 1 ∘ fun x => (b - a) * x + a) '' Icc 0 1 = _
    rw [image_comp, image_affine_Icc' (sub_pos.mpr hab)]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
  have hbase₂image : base₂ '' Icc (0 : ℝ) 1 =
      intrinsicAnnulusBoundary 1 '' Icc b (a + rampPeriod) := by
    change (intrinsicAnnulusBoundary 1 ∘
      fun x => (a + rampPeriod - b) * x + b) '' Icc 0 1 = _
    rw [image_comp, image_affine_Icc' (sub_pos.mpr hab₂)]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
  rw [hbase₁image] at hc₁ hfU₁ hfV₁
  rw [hbase₂image] at hc₂ hfU₂ hfV₂
  have hcircle (J : Set ℝ) :
      intrinsicAnnulusBoundary 1 '' J ⊆ standardAnnulusDomain := by
    rintro p ⟨x, _, rfl⟩
    change 1 ≤ ‖intrinsicAnnulusBoundary 1 x‖ ∧
      ‖intrinsicAnnulusBoundary 1 x‖ ≤ 2
    rw [m64Intrinsic_inner_boundary_norm]
    norm_num
  have halphaAnn (q : ℝ) (hq : q ∈ Icc (0 : ℝ) A) :
      alpha q ∈ standardAnnulusDomain := by
    by_cases hq0 : q = 0
    · subst q
      change 1 ≤ ‖alpha 0‖ ∧ ‖alpha 0‖ ≤ 2
      rw [ha0, m64Intrinsic_inner_boundary_norm]
      norm_num
    · have h := haInterior q ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2⟩
      exact ⟨h.1.le, h.2⟩
  have hbetaAnn (q : ℝ) (hq : q ∈ Icc (0 : ℝ) B) :
      beta q ∈ standardAnnulusDomain := by
    by_cases hq0 : q = 0
    · subst q
      change 1 ≤ ‖beta 0‖ ∧ ‖beta 0‖ ≤ 2
      rw [hb0, m64Intrinsic_inner_boundary_norm]
      norm_num
    · have h := hbInterior q ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2⟩
      exact ⟨h.1.le, h.2⟩
  have halphaShort : alpha '' Icc (0 : ℝ) s ⊆ standardAnnulusDomain := by
    rintro p ⟨q, hq, rfl⟩
    exact halphaAnn q ⟨hq.1, hq.2.trans hsA⟩
  have hbetaShort : beta '' Icc (0 : ℝ) t ⊆ standardAnnulusDomain := by
    rintro p ⟨q, hq, rfl⟩
    exact hbetaAnn q ⟨hq.1, hq.2.trans htB⟩
  have htrace₁ : frontier U₁ ⊆ standardAnnulusDomain := by
    rw [hfU₁]
    exact union_subset (hcircle _) (union_subset halphaShort hbetaShort)
  have htrace₂ : frontier U₂ ⊆ standardAnnulusDomain := by
    rw [hfU₂]
    exact union_subset (hcircle _) (union_subset hbetaShort halphaShort)
  have hc₁' : U₁ ∪ V₁ = (frontier U₁)ᶜ := by rwa [hfU₁]
  have hc₂' : U₂ ∪ V₂ = (frontier U₂)ᶜ := by rwa [hfU₂]
  have hf₁ : frontier U₁ = frontier V₁ := hfU₁.trans hfV₁.symm
  have hshared : frontier U₂ ⊆ frontier U₁ ∪ closedBall (0 : AnnulusCoordinates) 1 := by
    rw [hfU₂, hfU₁]
    rintro p (⟨x, hx, rfl⟩ | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩))
    · exact Or.inr (by simp [mem_closedBall, dist_zero_right,
        m64Intrinsic_inner_boundary_norm])
    · exact Or.inl (Or.inr (Or.inr ⟨q, hq, rfl⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨q, hq, rfl⟩))
  let m : ℝ := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  let p : AnnulusCoordinates := intrinsicAnnulusBoundary 1 m
  have hp : ‖p‖ = 1 := by
    dsimp [p]
    exact m64Intrinsic_inner_boundary_norm m
  have hp₁ : p ∈ frontier U₁ := by
    rw [hfU₁]
    exact Or.inl ⟨m, ⟨ham.le, hmb.le⟩, rfl⟩
  have hp₂ : p ∉ frontier U₂ := by
    rw [hfU₂]
    rintro (⟨x, hx, hxp⟩ | (⟨q, hq, hqp⟩ | ⟨q, hq, hqp⟩))
    · have hmperiod : a + rampPeriod - m < rampPeriod := by linarith
      have heq := m64Intrinsic_boundary_injOn_short_arc hmperiod
        (show x ∈ Icc m (a + rampPeriod) from ⟨by linarith [hx.1, hmb], hx.2⟩)
        (show m ∈ Icc m (a + rampPeriod) from ⟨le_rfl, by linarith⟩)
        (by simpa only [p] using hxp)
      linarith [hx.1, hmb, heq]
    · by_cases hq0 : q = 0
      · subst q
        rw [hb0] at hqp
        have heq := m64Intrinsic_boundary_injOn_short_arc hperiod
          (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
          (show m ∈ Icc a b from ⟨ham.le, hmb.le⟩) (by simpa only [p] using hqp)
        linarith [heq]
      · have h := hbInterior q ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2.trans htB⟩
        have h' : 1 < ‖beta q‖ ∧ ‖beta q‖ ≤ 2 := by simpa only [beta] using h
        rw [hqp] at h'
        exact (lt_irrefl (1 : ℝ))
          (by simpa only [p, m64Intrinsic_inner_boundary_norm] using h'.1)
    · by_cases hq0 : q = 0
      · subst q
        rw [ha0] at hqp
        have heq := m64Intrinsic_boundary_injOn_short_arc hperiod
          (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
          (show m ∈ Icc a b from ⟨ham.le, hmb.le⟩) (by simpa only [p] using hqp)
        linarith [heq]
      · have h := haInterior q ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2.trans hsA⟩
        have h' : 1 < ‖alpha q‖ ∧ ‖alpha q‖ ≤ 2 := by simpa only [alpha] using h
        rw [hqp] at h'
        exact (lt_irrefl (1 : ℝ))
          (by simpa only [p, m64Intrinsic_inner_boundary_norm] using h'.1)
  have hfirstPublic : ∀ x ∈ Icc (0 : ℝ) s, ∀ y ∈ Icc (0 : ℝ) t,
      u (a, x) = u (b, y) → x = s ∧ y = t := by
    intro x hx y hy hxy
    exact hfirst x hx y hy (by simpa only [alpha, beta] using hxy)
  obtain hann | hann₂ := m64Intrinsic_one_of_two_regions_is_annular
    hU₁ hV₁ hU₂ hV₂ hpV₁.isConnected.isPreconnected hbU₂ hbV₁ hd₁ hd₂ hc₁' hc₂'
      hf₁ hcompact₁ hcompact₂ htrace₁ htrace₂ hshared hp hp₁ hp₂
  · exact ⟨s, t, U₁, V₁, hs, hsA, ht, htB, by simpa only [alpha, beta] using hst,
      hfirstPublic,
      hU₁, hV₁, hpU₁, hpV₁, hbU₁, hbV₁, hd₁, hc₁',
      hf₁.symm, hcompact₁, hann, Or.inl hfU₁⟩
  · exact ⟨s, t, U₂, V₂, hs, hsA, ht, htB, by simpa only [alpha, beta] using hst,
      hfirstPublic,
      hU₂, hV₂, hpU₂, hpV₂, hbU₂, hbV₂, hd₂, hc₂',
      hfV₂.trans hfU₂.symm, hcompact₂, hann₂, Or.inr hfU₂⟩

end PoincareConjecture
