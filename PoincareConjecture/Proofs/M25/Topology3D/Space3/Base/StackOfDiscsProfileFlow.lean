import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfileExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfileChart

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable (a0 a1 : ℝ → ℝ) (b0 b1 : E2 → ℝ)
variable (ha0 : ContDiff ℝ ∞ a0) (ha1 : ContDiff ℝ ∞ a1)
variable (hb0 : ContDiff ℝ ∞ b0) (hb1 : ContDiff ℝ ∞ b1)
variable (hapos0 : ∀ v, 0 < a0 v) (hapos1 : ∀ v, 0 < a1 v)
variable (hbpos0 : ∀ x, 0 < b0 x) (hbpos1 : ∀ x, 0 < b1 x)
variable (habound0 : ∀ v, |v| < 1 → a0 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
variable (habound1 : ∀ v, |v| < 1 → a1 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
variable (T : OpenPartialHomeomorph (E2 × ℝ) E3)
variable (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
variable (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
variable (u : UnitTwoSphere)
variable (hheight : ∀ p ∈ T.source, inner ℝ (u : E3) (T p) = p.2)
variable (m sigma c lambda : ℝ) (hsign : |sigma| = 1) (hlambda : 0 < lambda)
variable (delta : ℝ) (hdelta : 0 < delta)
variable (W : Set E2) (hW : IsOpen W) (hcircle : sphere (0 : E2) 1 ⊆ W)
variable (ha0near : ∀ v, |v| < delta → a0 v = (Real.sqrt (1 - v ^ 2))⁻¹)
variable (ha1near : ∀ v, |v| < delta → a1 v = (Real.sqrt (1 - v ^ 2))⁻¹)
variable (hb0near : ∀ x ∈ W, b0 x = 1) (hb1near : ∀ x ∈ W, b1 x = 1)

local notation "M" => stackCapProfilePath a0 a1 b0 b1
local notation "cap" => stackPlacedProfileCap a0 a1 b0 b1 T m sigma c lambda
local notation "Qminus" =>
  Set.ofPred (fun q : UnitTwoSphere => Prod.snd (heightCoordinates (q : E3)) ≤ 0)
local notation "seam" => m + sigma * c
local notation "chi" => fun y : E3 => sigma * (inner ℝ (u : E3) y - seam)

include ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1 habound0 habound1
  hsource hT hTi hheight hsign hlambda hdelta hW hcircle
  ha0near ha1near hb0near hb1near in

theorem exists_stackPlacedProfileEvolution
    {V0 : Set E3} (hV0 : IsOpen V0)
    (htrackV0 : ∀ t ∈ Icc (-1 : ℝ) 2, ∀ q ∈ Qminus, cap t q ∈ V0) :
    ∃ N : Set E3, ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ C : Set E3,
      IsOpen N ∧ T '' (sphere (0 : E2) 1 ×ˢ ({seam} : Set ℝ)) ⊆ N ∧
      N ⊆ T.target ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (Φ p.1).symm p.2) ∧
      (∀ y, Φ 0 y = y) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2, ∀ q ∈ Qminus, Φ t (cap 0 q) = cap t q) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2, Φ t '' (cap 0 '' Qminus) = cap t '' Qminus) ∧
      IsCompact C ∧ C ⊆ ((V0 ∩ T.target) ∩ {y | chi y < 0}) \ N ∧
      (∀ t, tsupport (fun y => Φ t y - y) ⊆ C) ∧
      (∀ t, tsupport (fun y => (Φ t).symm y - y) ⊆ C) ∧
      (∀ t y, y ∉ C → Φ t y = y ∧ (Φ t).symm y = y) ∧
      (∀ t y, y ∈ N → Φ t y = y ∧ (Φ t).symm y = y) ∧
      ∀ t y, 0 ≤ chi y → Φ t y = y ∧ (Φ t).symm y = y := by
  have hsigma : sigma ≠ 0 := by
    intro hz
    simp [hz] at hsign
  let e := stackPlacedProfileChart a0 a1 b0 b1 ha0 ha1 hb0 hb1
    hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda.ne'
  obtain ⟨_O, N, _hO, _hEO, _hconstant, _hNdef, hN, hseam, hNtarget, hzero⟩ :=
    exists_stackPlacedProfileChart_common_germ a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda.ne'
      hsource hT hTi delta hdelta W hW hcircle ha0near ha1near hb0near hb1near
  let K : Set (ℝ × E3) :=
    (fun p : ℝ × UnitTwoSphere => (p.1, cap p.1 p.2)) ''
      (Icc (-1 : ℝ) 2 ×ˢ Qminus)
  obtain ⟨hK, _hKtarget⟩ := stackPlacedProfileCap_isCompact_track
    a0 a1 b0 b1 ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1
    T m sigma c lambda hsigma hlambda.ne' habound0 habound1 hsource hT
  have hchi : Continuous chi := continuous_const.mul
    ((innerSL ℝ (u : E3)).continuous.sub continuous_const)
  let Out : Set E3 := {y | chi y < 0}
  let U : Set (ℝ × E3) :=
    Ioo (-2 : ℝ) 3 ×ˢ ((V0 ∩ T.target) ∩ (Out ∪ N))
  have hOut : IsOpen Out := isOpen_lt hchi continuous_const
  have hU : IsOpen U := isOpen_Ioo.prod ((hV0.inter T.open_target).inter (hOut.union hN))
  have hKU : K ⊆ U := by
    rintro p ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
    have htarget : cap t q ∈ T.target := T.map_source
      (stackPlacedProfileCoordinates_mem_source a0 a1 b0 b1 ha0 ha1 hb0 hb1
        hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda
        habound0 habound1 hsource t q)
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      ⟨⟨htrackV0 t ht q hq, htarget⟩, ?_⟩⟩
    by_cases hqneg : (heightCoordinates (q : E3)).2 < 0
    · left
      change sigma * (inner ℝ (u : E3) (cap t q) - seam) < 0
      rw [stackPlacedProfileCap_signed_height a0 a1 b0 b1 ha0 ha1 hb0 hb1
        hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda
        habound0 habound1 hsource u hheight hsign t q]
      exact mul_neg_of_pos_of_neg hlambda
        ((stackCapProfilePath_snd_neg_iff a0 a1 b0 b1 hbpos0 hbpos1
          t (heightCoordinates (q : E3))).mpr hqneg)
    · right
      have hqzero : (heightCoordinates (q : E3)).2 = 0 :=
        le_antisymm hq (le_of_not_gt hqneg)
      have hxnorm : ‖(heightCoordinates (q : E3)).1‖ = 1 := by
        have hsphere := sphere_height_coordinates_sq q
        rw [hqzero] at hsphere
        nlinarith [norm_nonneg (heightCoordinates (q : E3)).1]
      have ha0zero : a0 0 = 1 := by
        simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.sqrt_one, inv_one]
          using ha0near 0 (by simpa only [abs_zero] using hdelta)
      have ha1zero : a1 0 = 1 := by
        simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.sqrt_one, inv_one]
          using ha1near 0 (by simpa only [abs_zero] using hdelta)
      have hblend : stackProfileBlend a0 a1 t 0 = 1 := by
        rw [stackProfileBlend, ha0zero, ha1zero]
        ring
      have hmodel : M t (heightCoordinates (q : E3)) =
          ((heightCoordinates (q : E3)).1, 0) := by
        simp only [stackCapProfilePath, hqzero, hblend, one_smul, mul_zero]
      apply hseam
      refine ⟨((heightCoordinates (q : E3)).1, seam),
        ⟨mem_sphere_zero_iff_norm.mpr hxnorm, mem_singleton _⟩, ?_⟩
      simp only [stackPlacedProfileCap, hmodel, mul_zero, add_zero]
  have hUtarget : U ⊆ e.target := by
    intro p hp
    rw [stackPlacedProfileChart_target]
    exact ⟨mem_univ _, hp.2.1.2⟩
  have he := stackPlacedProfileChart_contDiffOn a0 a1 b0 b1 ha0 ha1 hb0 hb1
    hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda.ne' hT hTi
  have hV : ContDiffOn ℝ ∞ (chartTimeField e) U :=
    (chartTimeField_contDiffOn e he.1 he.2).mono hUtarget
  let γ : ℝ → Qminus → E3 := fun t q => cap t q
  have htracks (q : Qminus) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) :
      (t, γ t q) ∈ K :=
    ⟨(t, (q : UnitTwoSphere)), ⟨Ioo_subset_Icc_self ht, q.2⟩, rfl⟩
  have hderiv (q : Qminus) (t : ℝ) (_ht : t ∈ Ioo (-1 : ℝ) 2) :
      HasDerivAt (fun z => γ z q) (chartTimeField e (t, γ t q)) t :=
    stackPlacedProfileCap_hasDerivAt a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda.ne'
      habound0 habound1 hsource hT hTi t q
  obtain ⟨Φ, C, hΦ, hΦi, hΦzero, hΦtrack, hCc, hCs, hsupport, hisupport, hfix, hfixN⟩ :=
    exists_ambient_evolution_of_localField_away (K := K) hK hU hKU
      (chartTimeField e) hV hN (fun t y hy _ => (hzero t y hy).2)
      γ (r := 0) (by norm_num) htracks hderiv
  have hCout : C ⊆ ((V0 ∩ T.target) ∩ {y | chi y < 0}) \ N := by
    intro y hy
    rcases hCs hy with ⟨⟨⟨t, z⟩, hp, hzy⟩, hyN⟩
    change z = y at hzy
    subst z
    refine ⟨⟨hp.2.1, ?_⟩, hyN⟩
    rcases hp.2.2 with hout | hin
    · exact hout
    · exact False.elim (hyN hin)
  have htrack (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) (q : UnitTwoSphere)
      (hq : q ∈ Qminus) : Φ t (cap 0 q) = cap t q :=
    hΦtrack ⟨q, hq⟩ t ht
  refine ⟨N, Φ, C, hN, hseam, hNtarget, hΦ, hΦi, hΦzero, htrack,
    ?_, hCc, hCout, hsupport, hisupport, hfix, hfixN, ?_⟩
  · intro t ht
    ext y
    constructor
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (htrack t ht q hq).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨cap 0 q, ⟨q, hq, rfl⟩, htrack t ht q hq⟩
  · intro t y hy
    apply hfix t y
    intro hyC
    exact (not_lt_of_ge hy) (hCout hyC).1.2

include ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1 habound0 habound1
  hsource hT hTi hheight hsign hlambda hdelta hW hcircle
  ha0near ha1near hb0near hb1near in

theorem exists_stackPlacedProfileEvolution_in_height_strip
    (B0 eta : ℝ) (_hB0 : 1 ≤ B0)
    (hbound : ∀ t : ℝ, ∀ q : UnitTwoSphere,
      |(M t (heightCoordinates (q : E3))).2| ≤ B0)
    (_heta : 0 < eta) (hsmall : lambda * B0 < eta) :
    ∃ N : Set E3, ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ C : Set E3,
      IsOpen N ∧ T '' (sphere (0 : E2) 1 ×ˢ ({seam} : Set ℝ)) ⊆ N ∧
      N ⊆ T.target ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (Φ p.1).symm p.2) ∧
      (∀ y, Φ 0 y = y) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2, ∀ q ∈ Qminus, Φ t (cap 0 q) = cap t q) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2, Φ t '' (cap 0 '' Qminus) = cap t '' Qminus) ∧
      IsCompact C ∧
      C ⊆ ((T.target ∩ {y | |inner ℝ (u : E3) y - seam| < eta}) ∩
        {y | chi y < 0}) \ N ∧
      (∀ t, tsupport (fun y => Φ t y - y) ⊆ C) ∧
      (∀ t, tsupport (fun y => (Φ t).symm y - y) ⊆ C) ∧
      (∀ t y, y ∉ C → Φ t y = y ∧ (Φ t).symm y = y) ∧
      (∀ t y, y ∈ N → Φ t y = y ∧ (Φ t).symm y = y) ∧
      ∀ t y, 0 ≤ chi y → Φ t y = y ∧ (Φ t).symm y = y := by
  let V0 : Set E3 := {y | |inner ℝ (u : E3) y - seam| < eta}
  have hV0 : IsOpen V0 := isOpen_lt
    (((innerSL ℝ (u : E3)).continuous.sub continuous_const).abs) continuous_const
  have htrackV0 (t : ℝ) (q : UnitTwoSphere) : cap t q ∈ V0 := by
    have hv := stackPlacedProfileCap_signed_height a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda
      habound0 habound1 hsource u hheight hsign t q
    have habs : |inner ℝ (u : E3) (cap t q) - seam| =
        lambda * |(M t (heightCoordinates (q : E3))).2| := by
      simpa only [abs_mul, hsign, one_mul, abs_of_pos hlambda] using congrArg abs hv
    change |inner ℝ (u : E3) (cap t q) - seam| < eta
    rw [habs]
    exact (mul_le_mul_of_nonneg_left (hbound t q) hlambda.le).trans_lt hsmall
  obtain ⟨N, Φ, C, hN, hseam, hNt, hΦ, hΦi, hzero, htrack, himage,
      hCc, hCs, hs, his, hfix, hfixN, hfixIn⟩ :=
    exists_stackPlacedProfileEvolution a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 habound0 habound1 T hsource hT hTi u hheight
      m sigma c lambda hsign hlambda delta hdelta W hW hcircle
      ha0near ha1near hb0near hb1near hV0 (fun t _ q _ => htrackV0 t q)
  refine ⟨N, Φ, C, hN, hseam, hNt, hΦ, hΦi, hzero, htrack, himage,
    hCc, ?_, hs, his, hfix, hfixN, hfixIn⟩
  intro y hy
  exact ⟨⟨⟨(hCs hy).1.1.2, (hCs hy).1.1.1⟩, (hCs hy).1.2⟩, (hCs hy).2⟩

end PoincareConjecture.M25.Topology3D
