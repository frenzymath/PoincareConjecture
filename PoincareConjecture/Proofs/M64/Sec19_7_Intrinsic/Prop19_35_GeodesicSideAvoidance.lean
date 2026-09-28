import PoincareConjecture.Proofs.M64.Mathlib.ClosedContactAvoidance
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicSideAgreement











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal Manifold ContDiff

namespace PoincareConjecture






theorem m64Intrinsic_constrained_minimizer_avoids_geodesic_side
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha) {a b : ℝ}
    (hinj : InjOn alpha (Icc a b))
    (hregular : ∀ p ∈ Ioo a b, deriv alpha p ≠ 0)
    (hgeo : G.IsGeodesicOn alpha (Ioo a b))
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
    (hstart : gamma 0 ∉ alpha '' Icc a b) (hend : gamma L = alpha b)
    (hcorner : ∀ u ∈ Ioo 0 L, gamma u ≠ alpha a) :
    ∀ u ∈ Ioo 0 L, gamma u ∉ alpha '' Icc a b := by
  apply m64ContinuousOn_avoids_closed_of_local_contact hc
    (isCompact_Icc.image ha.continuous).isClosed hstart
  intro u hu hmem
  obtain ⟨p, hp, hpoint⟩ := hmem
  have hpa : a < p := by
    rcases hp.1.eq_or_lt with heq | hlt
    · exact False.elim (hcorner u hu (by rw [heq]; exact hpoint.symm))
    · exact hlt
  have hpb : p < b := by
    rcases hp.2.eq_or_lt with heq | hlt
    · have hmeet : gamma u = gamma L := by rw [hend, ← heq]; exact hpoint.symm
      have htime := hginj ⟨hu.1.le, hu.2.le⟩ ⟨hu.1.le.trans hu.2.le, le_rfl⟩ hmeet
      exact False.elim (hu.2.ne htime)
    · exact hlt
  obtain ⟨_, _, _, hnear⟩ := m64Intrinsic_constrained_minimizer_geodesic_side_agreement
    G ha hinj ⟨hpa, hpb⟩ (hregular p ⟨hpa, hpb⟩) hgeo hW (hseparate p ⟨hpa, hpb⟩)
    hU hV hdisj hfU hfV hK hc hconf hlip hmin hu hpoint.symm
  filter_upwards [hnear] with t ht
  exact image_mono Ioo_subset_Icc_self ht

end PoincareConjecture
