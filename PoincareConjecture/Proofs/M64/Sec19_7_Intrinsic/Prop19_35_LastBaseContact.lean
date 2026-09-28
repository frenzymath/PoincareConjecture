import PoincareConjecture.Proofs.M64.Mathlib.LastClosedContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InteriorGeodesic
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LastContactTangency
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointUnitSpeed










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_constrained_minimizer_last_base_contact
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha) {a b : ℝ}
    (hinj : InjOn alpha (Icc a b)) (hregular : ∀ p ∈ Ioo a b, deriv alpha p ≠ 0)
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W)
    (hseparate : ∀ p ∈ Ioo a b, alpha p ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc a b ∪ W) (hfV : frontier V = frontier U)
    (hK : IsCompact (closure U)) {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hc : ContinuousOn gamma (Icc 0 L))
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
    ∃ u p : ℝ, ∃ v : AnnulusCoordinates, ∃ c : ℝ,
      u ∈ Ioo 0 L ∧ p ∈ Ioo a b ∧ gamma u = alpha p ∧
      MapsTo gamma (Ioo u L) (interior (closure U)) ∧
      G.IsGeodesicOn gamma (Ioo u L) ∧
      (∀ t ∈ Ioo u L, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ gamma t) ∧
      HasDerivWithinAt gamma v (Ioi u) u ∧ v ≠ 0 ∧
      G.tangentNorm (gamma u) v = 1 ∧ c ≠ 0 ∧ v = c • deriv alpha p := by
  obtain ⟨u, hu, humem, hlast⟩ := m64ContinuousOn_exists_last_closed_contact hc
    (isCompact_Icc.image ha.continuous).isClosed hend hcontact
  obtain ⟨p, hp, hpoint⟩ := humem
  have hpa : a < p := lt_of_le_of_ne hp.1 (fun heq =>
    (hcorners u hu).1 (hpoint.symm.trans (congrArg alpha heq.symm)))
  have hpb : p < b := lt_of_le_of_ne hp.2 (fun heq =>
    (hcorners u hu).2 (hpoint.symm.trans (congrArg alpha heq)))
  have hinside : MapsTo gamma (Ioo u L) (interior (closure U)) := by
    intro t ht
    have htfull : t ∈ Ioo 0 L := ⟨hu.1.trans ht.1, ht.2⟩
    by_contra hout
    have hfront : gamma t ∈ frontier (closure U) :=
      ⟨subset_closure (hconf (Ioo_subset_Icc_self htfull)), hout⟩
    have hf : gamma t ∈ alpha '' Icc a b ∪ W :=
      hfU ▸ frontier_closure_subset hfront
    exact hf.elim (hlast t ⟨ht.1, ht.2.le⟩) (hside t htfull)
  obtain ⟨hgeo, hsmooth⟩ :=
    m64Intrinsic_constrained_minimizer_interior_geodesic G hK hlip hmin
  have houtGeo : G.IsGeodesicOn gamma (Ioo u L) :=
    fun t ht => hgeo t ⟨⟨hu.1.trans ht.1, ht.2⟩, hinside ht⟩
  obtain ⟨v, hv, hvne, c, hcne, hvc⟩ :=
    m64Intrinsic_constrained_minimizer_last_contact_tangent G ha hinj ⟨hpa, hpb⟩
      (hregular p ⟨hpa, hpb⟩) hW (hseparate p ⟨hpa, hpb⟩)
      hU hV hdisj hfU hfV hK hc hconf hlip hmin hu hpoint.symm houtGeo
  have hvunit : G.tangentNorm (gamma u) v = 1 :=
    m64Intrinsic_compact_geodesic_right_derivative_unit G hK hu.2 houtGeo
      (fun t ht => hconf ⟨hu.1.le.trans ht.1.le, ht.2.le⟩)
      (hc.continuousAt (Icc_mem_nhds hu.1 hu.2)).continuousWithinAt
      (fun t ht => m64Intrinsic_constrained_minimizer_interior_unit_speed G hK hlip hmin
        ⟨hu.1.trans ht.1, ht.2⟩ (hinside ht)) hv
  exact ⟨u, p, v, c, hu, ⟨hpa, hpb⟩, hpoint.symm, hinside, houtGeo,
    fun t ht => hsmooth t ⟨hu.1.trans ht.1, ht.2⟩ (hinside ht), hv, hvne, hvunit, hcne, hvc⟩

end PoincareConjecture
