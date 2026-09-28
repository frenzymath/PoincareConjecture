import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LastBaseContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactGeodesicRepresentative
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanCorner

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_constrained_minimizer_smooth_last_base_contact
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha) {a b : ℝ}
    (hinj : InjOn alpha (Icc a b)) (hregular : ∀ p ∈ Ioo a b, deriv alpha p ≠ 0)
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W)
    (hseparate : ∀ p ∈ Ioo a b, alpha p ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc a b ∪ W) (hfV : frontier V = frontier U)
    (hK : IsCompact (closure U)) {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hc : ContinuousOn gamma (Icc 0 L)) (hginj : InjOn gamma (Icc 0 L))
    (hconf : MapsTo gamma (Icc 0 L) (closure U))
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ c ∈ Icc 0 L, ∀ d ∈ Icc 0 L, c ≤ d →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma c → tau 1 = gamma d → MapsTo tau (Icc 0 1) (closure U) →
        ENNReal.ofReal (d - c) ≤ m64IntrinsicCurveVariation G tau 0 1)
    (hside : ∀ t ∈ Ioo 0 L, gamma t ∉ W)
    (hcorners : ∀ t ∈ Ioo 0 L, gamma t ≠ alpha a ∧ gamma t ≠ alpha b)
    (hend : gamma L ∉ alpha '' Icc a b)
    (hcontact : ∃ t ∈ Ioo 0 L, gamma t ∈ alpha '' Icc a b) :
    ∃ u p c : ℝ, ∃ eta : ℝ → AnnulusCoordinates,
      u ∈ Ioo 0 L ∧ p ∈ Ioo a b ∧ gamma u = alpha p ∧ c ≠ 0 ∧
      ContDiff ℝ ∞ eta ∧ EqOn eta gamma (Icc u L) ∧ InjOn eta (Icc u L) ∧
      MapsTo eta (Ioo u L) U ∧ G.IsGeodesicOn eta (Icc u L) ∧
      deriv eta u = c • deriv alpha p ∧
      (∀ t ∈ Icc u L, G.tangentNorm (eta t) (deriv eta t) = 1) ∧
      (∀ t ∈ Icc u L, deriv eta t ≠ 0) := by
  obtain ⟨u, p, v, c, hu, hp, hup, hinside, hgeo, _, hv, _, hunit, hcne, hvc⟩ :=
    m64Intrinsic_constrained_minimizer_last_base_contact G ha hinj hregular hW
      hseparate hU hV hdisj hfU hfV hK hc hconf hlip hmin hside hcorners hend hcontact
  have hsub : Icc u L ⊆ Icc 0 L := Icc_subset_Icc hu.1.le le_rfl
  obtain ⟨eta, heta, heq, hegeo, hdu, _⟩ :=
    m64Intrinsic_compact_geodesic_smooth_representative G hK hu.2 (hc.mono hsub)
      hgeo (fun t ht => hconf (hsub (Ioo_subset_Icc_self ht)))
  have hderiv : deriv eta u = v :=
    (hdu.derivWithin (uniqueDiffWithinAt_Ioi u)).symm.trans
      (hv.derivWithin (uniqueDiffWithinAt_Ioi u))
  have hunit0 : G.tangentNorm (eta u) (deriv eta u) = 1 := by
    rw [heq (left_mem_Icc.mpr hu.2.le), hderiv]
    exact hunit
  have hspeed (t : ℝ) (ht : t ∈ Icc u L) :
      G.tangentNorm (eta t) (deriv eta t) = 1 := by
    have hd (s : ℝ) (hs : s ∈ Icc u L) :
        HasDerivWithinAt (fun x => G.tangentNorm (eta x) (deriv eta x)) 0 (Icc u L) s := by
      have hh := hegeo.hasDerivAt_tangentNorm_zero hs
      change HasDerivAt (fun x => G.tangentNorm (eta x) (curveVelocity (n := 2) eta x)) 0 s at hh
      simp_rw [m64Intrinsic_curveVelocity_eq_deriv] at hh
      exact hh.hasDerivWithinAt
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (show ∀ s ∈ Icc u L, ‖(0 : ℝ)‖ ≤ 0 from fun _ _ => by simp)
      (convex_Icc u L) (left_mem_Icc.mpr hu.2.le) ht
    have hequal : G.tangentNorm (eta t) (deriv eta t) =
        G.tangentNorm (eta u) (deriv eta u) := by
      simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hh
    exact hequal.trans hunit0
  refine ⟨u, p, c, eta, hu, hp, hup, hcne, heta, heq, ?_, ?_, hegeo,
    hderiv.trans hvc, hspeed, ?_⟩
  · intro s hs t ht hst
    apply hginj (hsub hs) (hsub ht)
    rwa [← heq hs, ← heq ht]
  · intro t ht
    rw [heq (Ioo_subset_Icc_self ht)]
    exact (m64Intrinsic_jordan_interior_closure hU hV hdisj hfV.symm).1 ▸ hinside ht
  · intro t ht hzero
    have hh := hspeed t ht
    simp only [hzero, RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero] at hh
    exact zero_ne_one hh

end PoincareConjecture
