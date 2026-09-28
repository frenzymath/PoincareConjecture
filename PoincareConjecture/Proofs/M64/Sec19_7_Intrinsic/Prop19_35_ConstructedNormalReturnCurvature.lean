import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalReturnRegionCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcRegionTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_Continuation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_constructed_circle_geodesic_region_curvature_lower_bound
    (N : IntrinsicAnnulus)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (ha0 : deriv alpha 0 ≠ 0)
    (hareg : ∀ p ∈ Ioo (0 : ℝ) A, deriv alpha p ≠ 0)
    (hgeo : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunit : ∀ p ∈ Icc 0 B,
      N.metric.inner (beta p) (deriv beta p) (deriv beta p) = 1)
    (horth : N.metric.inner (alpha 0) (deriv alpha 0) (deriv beta 0) = 0)
    (hterminal : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {a b0 : ℝ} (hab : a ≤ b0)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b0))
    (hcircle : alpha '' Icc 0 A = intrinsicAnnulusBoundary 1 '' Icc a b0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain) :
    Real.pi / 2 - intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b0 ≤
      ∫ x in closure U, N.connection.scalarCurvature x / 2 ∂N.metric.volumeMeasure := by
  have hbreg (p : ℝ) (hp : p ∈ Icc 0 B) : deriv beta p ≠ 0 := by
    intro hz
    have hu := hunit p hp
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hind0 : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates) := by
    rw [linearIndependent_fin2]
    refine ⟨hbreg 0 ⟨le_rfl, hB.le⟩, ?_⟩
    intro c heq
    change c • deriv beta 0 = deriv alpha 0 at heq
    have hbb := N.metric.pos (alpha 0) (deriv beta 0) (hbreg 0 ⟨le_rfl, hB.le⟩)
    have h := horth
    rw [← heq, map_smul, smul_apply, smul_eq_mul] at h
    have hc : c = 0 := (mul_eq_zero.mp h).resolve_right hbb.ne'
    apply ha0
    simpa only [hc, zero_smul] using heq.symm
  have hmeetImages : (alpha '' Icc 0 A) ∩ (beta '' Icc 0 B) ⊆
      {alpha 0, alpha A} := by
    rintro x ⟨⟨s, hs, hsx⟩, ⟨t, ht, htx⟩⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases hmeet s hs t ht (hsx.trans htx.symm) with h | h
    · exact Or.inl (hsx.symm.trans (congrArg alpha h.1))
    · exact Or.inr (hsx.symm.trans (congrArg alpha h.1))
  have hcompact : IsCompact (closure U) :=
    m64Intrinsic_standardAnnulus_isCompact.of_isClosed_subset isClosed_closure hsub
  obtain ⟨m, face, F, b, hF, hFi, hsource, hcarrier, hboundary, hfront, hinter,
      hcover, v0, v1, hv0, hv1⟩ :=
    m64Intrinsic_exists_two_arc_region_triangulation ha hb hA hB hai hbi hareg
      (fun p hp => hbreg p (Ioo_subset_Icc_self hp)) hmeetImages hbase hend hind0 hterminal
      hU hV hdisj hfU hfV hcompact
  exact m64Intrinsic_circle_geodesic_region_curvature_lower_bound N face F b
    hF hFi hsource hcarrier hboundary hinter hfront ha hb hA hB hai hbi hbase hend hmeet
    ha0 hareg hgeo hunit horth hab hcircleInj hcircle hU hV hdisj hfU hfV hclosure
    hVconn hinward hsub hcover v0 v1 hv0 hv1

end PoincareConjecture
