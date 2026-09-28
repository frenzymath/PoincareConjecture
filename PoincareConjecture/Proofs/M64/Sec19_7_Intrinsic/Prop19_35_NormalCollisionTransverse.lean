import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_OppositeGeodesicJoin
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RawInnerNormalReturn

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_short_normal_collision_transverse
    (N : IntrinsicAnnulus)
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {x y A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 x)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 y)
    (haInterior : ∀ t ∈ Ioc 0 A, 1 < ‖alpha t‖)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖)
    (hga : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgb : N.metric.IsGeodesicOn beta (Icc 0 B))
    (haUnit : N.metric.inner (alpha 0) (deriv alpha 0) (deriv alpha 0) = 1)
    (hbUnit : N.metric.inner (beta 0) (deriv beta 0) (deriv beta 0) = 1)
    (haOrth : N.metric.inner (intrinsicAnnulusBoundary 1 x)
      (deriv (intrinsicAnnulusBoundary 1) x) (deriv alpha 0) = 0)
    (hbOrth : N.metric.inner (intrinsicAnnulusBoundary 1 y)
      (deriv (intrinsicAnnulusBoundary 1) y) (deriv beta 0) = 0)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 x) (deriv alpha 0))
    (hmeet : alpha A = beta B)
    (hcontact : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → s = A ∧ t = B)
    (hperiod : |y - x| < rampPeriod)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc (min x y) (max x y) ∪
      (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta r mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hshort : intrinsicBoundaryLength N.metric 1 (min x y) (max x y) ≤ r) :
    LinearIndependent ℝ (![-deriv alpha A, -deriv beta B] :
      Fin 2 → AnnulusCoordinates) := by
  have hstart : alpha 0 ≠ beta 0 := by
    intro heq
    exact hA.ne (hcontact 0 ⟨le_rfl, hA.le⟩ 0 ⟨le_rfl, hB.le⟩ heq).1
  have hau : ∀ t ∈ Icc 0 A,
      N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1 := by
    have h := m64Intrinsic_geodesic_velocity_unit N hA hga Subset.rfl
      (by simpa only [m64Intrinsic_curveVelocity_eq_deriv] using haUnit)
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using h
  have hbu : ∀ t ∈ Icc 0 B,
      N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1 := by
    have h := m64Intrinsic_geodesic_velocity_unit N hB hgb Subset.rfl
      (by simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hbUnit)
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using h
  rcases m64Intrinsic_inward_meeting_opposite_or_transverse N.metric ha hb hga hgb
      hA.le hB.le (by rw [ha0, m64Intrinsic_inner_boundary_norm])
      (by rw [hb0, m64Intrinsic_inner_boundary_norm]) hstart haInterior hbInterior
      (hau A ⟨hA.le, le_rfl⟩) (hbu B ⟨hB.le, le_rfl⟩) hmeet with hopp | hind
  · obtain ⟨gamma, hleft, hright, hg, hgeo, hgi, hg0, hg1, himage⟩ :=
      m64Intrinsic_opposite_first_contact_embedded_join N.metric ha hb hga hgb hA hB
        hmeet hopp hai hbi hcontact
    have hd0 : deriv gamma 0 = deriv alpha 0 := by
      have heq : gamma =ᶠ[𝓝 (0 : ℝ)] alpha := by
        filter_upwards [Iio_mem_nhds hA] with t ht
        exact hleft t ht.le
      exact heq.deriv_eq
    have hd1 : deriv gamma (A + B) = -deriv beta 0 := by
      have heq : gamma =ᶠ[𝓝 (A + B)] (fun t => beta (A + B - t)) := by
        filter_upwards [Ioi_mem_nhds (show A < A + B by linarith)] with t ht
        exact hright t ht.le
      rw [heq.deriv_eq, deriv_comp_const_sub, sub_self]
    have hbne : deriv beta 0 ≠ 0 := by
      intro hz
      simp only [hz, map_zero] at hbUnit
      norm_num at hbUnit
    have hcne : deriv (intrinsicAnnulusBoundary 1) y ≠ 0 := by
      intro hz
      have hpos := m64Intrinsic_boundarySpeed_pos N one_ne_zero y
      simp only [intrinsicBoundarySpeed, RiemannianMetric.tangentNorm,
        m64Intrinsic_curveVelocity_eq_deriv, hz, map_zero, Real.sqrt_zero] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    have hterminal : LinearIndependent ℝ
        (![deriv (intrinsicAnnulusBoundary 1) y, deriv gamma (A + B)] :
          Fin 2 → AnnulusCoordinates) := by
      rw [hd1, LinearIndependent.pair_neg_right_iff, linearIndependent_fin2]
      refine ⟨hbne, ?_⟩
      intro c heq
      change c • deriv beta 0 = deriv (intrinsicAnnulusBoundary 1) y at heq
      have hbb := N.metric.pos (intrinsicAnnulusBoundary 1 y) (deriv beta 0) hbne
      have h := hbOrth
      rw [← heq, map_smul, smul_apply, smul_eq_mul] at h
      have hc : c = 0 := (mul_eq_zero.mp h).resolve_right hbb.ne'
      apply hcne
      simpa only [hc, zero_smul] using heq.symm
    have hinside : ∀ t ∈ Ioo 0 (A + B), 1 < ‖gamma t‖ := by
      intro t ht
      by_cases htA : t ≤ A
      · rw [hleft t htA]
        exact haInterior t ⟨ht.1, htA⟩
      · rw [hright t (le_of_not_ge htA)]
        exact hbInterior (A + B - t) ⟨by linarith [ht.2], by linarith⟩
    have hfront : frontier U =
        intrinsicAnnulusBoundary 1 '' Icc (min x y) (max x y) ∪
          gamma '' Icc 0 (A + B) := by
      rw [himage]
      exact hfU
    exact (m64Intrinsic_no_short_transverse_inner_return N hg (by linarith) hgi
      (hg0.trans ha0) (hg1.trans hb0) hinside hgeo
      (by rw [hg0, hd0]; exact haUnit) (by rw [hd0]; exact haOrth)
      (by rw [hd0]; exact hinward) hterminal hperiod hU hV hdisj hfront hfV
      hclosure hVconn hsub hK hturn harea hbudget hshort).elim
  · exact LinearIndependent.pair_neg_left_iff.mpr hind

end PoincareConjecture
