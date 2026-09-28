import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ActualNormalComparison
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_UniformComparisonConstants
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_UniformNormalGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64IntrinsicAnnulusComparison : M64IntrinsicAnnulusComparison := by
  intro delta r K hdelta hdeltaSmall hr
  have hdelta1 : delta < 1 := hdeltaSmall.trans (by norm_num)
  obtain ⟨q, alpha, hq, hqr, _, hmodel, halpha0, halpha, hsmall, hrhoSmall⟩ :=
    m64Intrinsic_exists_comparison_base_scale K hdelta hdeltaSmall hr
  obtain ⟨R0, hR0, _, hnormal⟩ :=
    m64Intrinsic_exists_uniform_normal_geometry K hdelta hdelta1 halpha0
  obtain ⟨h, mu, hh, hhq, hhR0, hmu, hmuArea, hbudget⟩ :=
    m64Intrinsic_exists_comparison_area_cutoff K hdeltaSmall hq hR0
  refine ⟨mu, hmu, ?_⟩
  intro N hK hfirst hturn harea
  obtain ⟨normal, e, height, _, he, hheight, _, _, _, hn, hbase, hderiv,
      hstop, htube, hmetric⟩ := hnormal h hh hhR0 N hK
  have horth (p : ℝ) : N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0 := by
    rw [N.metric.symm]
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using (hn p).2.1
  have hgeo (p : ℝ) :
      N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (height p)) := by
    obtain ⟨S, I, _, _, hp, hsub, hgeodesic⟩ := htube p
    exact fun t ht => hgeodesic p hp t (hsub ht)
  have himage (p : ℝ) : ∀ t ∈ Icc 0 (height p), e !₂[p, t] ∈ standardAnnulusDomain := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with ht0 | htpos
    · rw [← ht0, hbase p]
      change 1 ≤ ‖intrinsicAnnulusBoundary 1 p‖ ∧ ‖intrinsicAnnulusBoundary 1 p‖ ≤ 2
      rw [m64Intrinsic_inner_boundary_norm]
      exact ⟨le_rfl, by norm_num⟩
    · rcases lt_or_eq_of_le ht.2 with htlt | hteq
      · exact ⟨((hstop p).2.2.1 t ⟨htpos, htlt⟩).1.le,
          ((hstop p).2.2.1 t ⟨htpos, htlt⟩).2.le⟩
      · simpa only [hteq] using (hstop p).2.2.2.1
  exact (m64Intrinsic_comparison_of_actual_normal_geometry N hK hdelta hdeltaSmall
    hq hqr hh hhq hturn halpha.symm.le hsmall hrhoSmall (hqr.trans_lt hfirst)
    harea hbudget hmodel (harea.trans_le hmuArea) e he normal height hheight hbase hderiv
    (fun p => (hn p).1) horth (fun p => (hn p).2.2)
    (fun p => ⟨(hstop p).1, (hstop p).2.2.2.2⟩) (fun p => (hstop p).2.1)
    (fun p => (hstop p).2.2.1) himage hgeo (fun p hp t ht => (hmetric p hp t ht).1)).le

end PoincareConjecture
