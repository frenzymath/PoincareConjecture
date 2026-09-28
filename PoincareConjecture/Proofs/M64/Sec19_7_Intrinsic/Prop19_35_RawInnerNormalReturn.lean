import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConstructedNoShortNormalReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InnerReturnRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalMetric












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_no_short_transverse_inner_return
    (N : IntrinsicAnnulus)
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {x y T : ℝ} (hT : 0 < T) (hgi : InjOn gamma (Icc 0 T))
    (h0 : gamma 0 = intrinsicAnnulusBoundary 1 x)
    (h1 : gamma T = intrinsicAnnulusBoundary 1 y)
    (hinside : ∀ t ∈ Ioo 0 T, 1 < ‖gamma t‖)
    (hgeo : N.metric.IsGeodesicOn gamma (Icc 0 T))
    (hunit0 : N.metric.inner (gamma 0) (deriv gamma 0) (deriv gamma 0) = 1)
    (horth : N.metric.inner (intrinsicAnnulusBoundary 1 x)
      (deriv (intrinsicAnnulusBoundary 1) x) (deriv gamma 0) = 0)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 x) (deriv gamma 0))
    (hterminal : LinearIndependent ℝ
      (![deriv (intrinsicAnnulusBoundary 1) y, deriv gamma T] :
        Fin 2 → AnnulusCoordinates))
    (hperiod : |y - x| < rampPeriod)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U =
      intrinsicAnnulusBoundary 1 '' Icc (min x y) (max x y) ∪ gamma '' Icc 0 T)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta r mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hshort : intrinsicBoundaryLength N.metric 1 (min x y) (max x y) ≤ r) :
    False := by
  have hxy : x ≠ y := by
    intro heq
    have hpoints : gamma 0 = gamma T := by rw [h0, h1, heq]
    exact hT.ne (hgi ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hpoints)
  have hd : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  let p : ℝ → ℝ := fun s => x + (y - x) * s
  let alpha : ℝ → AnnulusCoordinates := intrinsicAnnulusBoundary 1 ∘ p
  have hp0 : p 0 = x := by simp only [p, mul_zero, add_zero]
  have hp1 : p 1 = y := by dsimp only [p]; ring
  have hpimage : p '' Icc (0 : ℝ) 1 = Icc (min x y) (max x y) := by
    change ((fun z => x + z) ∘ fun s => (y - x) * s) '' Icc (0 : ℝ) 1 = _
    rw [← uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num), image_comp,
      image_const_mul_uIcc, image_const_add_uIcc]
    simp only [mul_zero, mul_one, add_zero, show x + (y - x) = y by ring]
    rfl
  have hparam (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : p s ∈ Icc (min x y) (max x y) := by
    rw [← hpimage]
    exact mem_image_of_mem p hs
  have hperiod' : max x y - min x y < rampPeriod := by
    simpa only [max_sub_min_eq_abs] using hperiod
  have hcInj := m64Intrinsic_boundary_injOn_short_arc hperiod'
  have halpha : ContDiff ℝ ∞ alpha :=
    (m64Intrinsic_contDiff_boundary 1).comp (by dsimp only [p]; fun_prop)
  have haInj : InjOn alpha (Icc (0 : ℝ) 1) := by
    intro s hs t ht heq
    have heq' := hcInj (hparam s hs) (hparam t ht) heq
    exact mul_left_cancel₀ hd (add_left_cancel heq')
  have ha0 : alpha 0 = intrinsicAnnulusBoundary 1 x :=
    congrArg (intrinsicAnnulusBoundary 1) hp0
  have ha1 : alpha 1 = intrinsicAnnulusBoundary 1 y :=
    congrArg (intrinsicAnnulusBoundary 1) hp1
  have haimage : alpha '' Icc (0 : ℝ) 1 =
      intrinsicAnnulusBoundary 1 '' Icc (min x y) (max x y) := by
    change (intrinsicAnnulusBoundary 1 ∘ p) '' Icc (0 : ℝ) 1 = _
    rw [image_comp, hpimage]
  have hpderiv (s : ℝ) : HasDerivAt p (y - x) s := by
    simpa only [p, mul_one] using! ((hasDerivAt_id s).const_mul (y - x)).const_add x
  have haderiv (s : ℝ) : deriv alpha s =
      (y - x) • deriv (intrinsicAnnulusBoundary 1) (p s) :=
    (((m64Intrinsic_contDiff_boundary 1).differentiable (by simp) (p s)).hasDerivAt.scomp
      s (hpderiv s)).deriv
  have hcRegular (s : ℝ) : deriv (intrinsicAnnulusBoundary 1) s ≠ 0 := by
    intro hz
    have hpos := m64Intrinsic_boundarySpeed_pos N one_ne_zero s
    simp only [intrinsicBoundarySpeed, RiemannianMetric.tangentNorm,
      m64Intrinsic_curveVelocity_eq_deriv, hz, map_zero, Real.sqrt_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have haRegular (s : ℝ) : deriv alpha s ≠ 0 := by
    rw [haderiv]
    exact smul_ne_zero hd (hcRegular (p s))
  have hmeet : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 T,
      alpha s = gamma t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = T) := by
    intro s hs t ht heq
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl ⟨haInj hs ⟨le_rfl, zero_le_one⟩ (heq.trans (h0.trans ha0.symm)), rfl⟩
    by_cases htT : t = T
    · subst t
      exact Or.inr ⟨haInj hs ⟨zero_le_one, le_rfl⟩ (heq.trans (h1.trans ha1.symm)), rfl⟩
    have hnorm := hinside t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htT⟩
    rw [← heq] at hnorm
    exact False.elim ((lt_irrefl (1 : ℝ))
      (by simpa only [alpha, Function.comp_apply, m64Intrinsic_inner_boundary_norm] using hnorm))
  have hunit : ∀ t ∈ Icc 0 T,
      N.metric.inner (gamma t) (deriv gamma t) (deriv gamma t) = 1 := by
    have h := m64Intrinsic_geodesic_velocity_unit N hT hgeo Subset.rfl
      (by simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hunit0)
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using h
  have haorth : N.metric.inner (alpha 0) (deriv alpha 0) (deriv gamma 0) = 0 := by
    rw [ha0, haderiv, hp0]
    simp only [map_smul, smul_apply, smul_eq_mul, horth, mul_zero]
  have haterminal : LinearIndependent ℝ
      (![-deriv alpha 1, -deriv gamma T] : Fin 2 → AnnulusCoordinates) := by
    rw [haderiv, hp1, LinearIndependent.pair_neg_left_iff,
      LinearIndependent.pair_neg_right_iff]
    have hscaled : LinearIndependent ℝ
        (![(y - x) • deriv (intrinsicAnnulusBoundary 1) y,
          (1 : ℝ) • deriv gamma T] : Fin 2 → AnnulusCoordinates) :=
      (LinearIndependent.pair_smul_smul_iff (isUnit_iff_ne_zero.mpr hd) isUnit_one).mpr hterminal
    simpa only [one_smul] using hscaled
  have hfront : frontier U = alpha '' Icc (0 : ℝ) 1 ∪ gamma '' Icc 0 T := by
    rw [haimage]
    exact hfU
  exact m64Intrinsic_constructed_no_short_normal_return N halpha hg zero_lt_one hT
    haInj hgi (h0.trans ha0.symm) (h1.trans ha1.symm) hmeet (haRegular 0)
    (fun s _ => haRegular s) hgeo hunit haorth haterminal min_le_max
    hcInj haimage hU hV hdisj hfront hfV hclosure hVconn (ha0.symm ▸ hinward) hsub
    hK hturn harea hbudget (by linarith only [hperiod']) hshort

end PoincareConjecture
