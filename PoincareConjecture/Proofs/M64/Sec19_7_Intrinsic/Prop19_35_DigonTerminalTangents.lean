import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonInitialTangents
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_OppositeGeodesicJoin
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ClosedCornerRayInjectivity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture

theorem m64Intrinsic_digon_terminal_velocity_ne
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hgeoA : G.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : G.IsGeodesicOn beta (Icc 0 B)) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B)) :
    deriv alpha A ≠ deriv beta B := by
  have reverse_geo {eta : ℝ → AnnulusCoordinates} {T : ℝ}
      (hg : G.IsGeodesicOn eta (Icc 0 T)) :
      G.IsGeodesicOn (fun t => eta (T - t)) (Icc 0 T) := by
    intro t ht
    have h := hg.comp_affine (-1) T t
      (show -1 * t + T ∈ Icc 0 T from ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using h
  have hcontacts : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha (A - s) = beta (B - t) → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B) := by
    intro s hs t ht he
    rcases hmeet (A - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      (B - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ he with h | h
    · exact Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩
    · exact Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩
  have hne := m64Intrinsic_digon_initial_velocity_ne G hA hB
    (reverse_geo hgeoA) (reverse_geo hgeoB) (by simpa only [sub_zero] using hend) hcontacts
  intro he
  apply hne
  simpa only [deriv_comp_const_sub, sub_zero] using congrArg Neg.neg he

theorem m64Intrinsic_digon_terminal_transverse_at_convex_corner
    (N : IntrinsicAnnulus) {K : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfront : frontier U = frontier V) (hsub : closure U ⊆ standardAnnulusDomain)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (hconfA : MapsTo alpha (Icc 0 A) (closure U))
    (hconfB : MapsTo beta (Icc 0 B) (closure U))
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (alpha 0)) (hzero : phi (alpha 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (alpha 0),
      z ∈ closure U → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) :
    LinearIndependent ℝ (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates) := by
  have hopp : deriv alpha A ≠ -deriv beta B := by
    intro he
    obtain ⟨gamma, hleft, _, hg, hgeo, hg0, hgT, himage⟩ :=
      m64Intrinsic_opposite_meeting_smooth_geodesic_join N.metric ha hb
        hgeoA hgeoB hA hB hend.symm he
    have hnear : gamma =ᶠ[𝓝 (0 : ℝ)] alpha := by
      filter_upwards [Iio_mem_nhds hA] with t ht
      exact hleft t ht.le
    have hzeroUnit : N.metric.inner (gamma 0) (deriv gamma 0 : AnnulusCoordinates)
        (deriv gamma 0 : AnnulusCoordinates) = 1 := by
      rw [hg0, hnear.deriv_eq]
      exact hunitA 0 ⟨le_rfl, hA.le⟩
    have hunit : ∀ t ∈ Icc 0 (A + B),
        N.metric.inner (gamma t) (deriv gamma t) (deriv gamma t) = 1 := by
      intro t ht
      simpa only [m64Intrinsic_curveVelocity_eq_deriv] using
        m64Intrinsic_geodesic_velocity_unit N (add_pos hA hB) hgeo Subset.rfl
          (by simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hzeroUnit) t ht
    have hconf : MapsTo gamma (Icc 0 (A + B)) (closure U) := by
      apply mapsTo_iff_image_subset.mpr
      rw [himage]
      exact union_subset (mapsTo_iff_image_subset.mp hconfA) (mapsTo_iff_image_subset.mp hconfB)
    have hinj := m64Intrinsic_closed_corner_ray_injOn N hK hsmall
      hU hV hpV hbV hUV hcover hfront hsub hg hgeo hunit hconf L
      (hg0.symm ▸ hphi) (hg0.symm ▸ hzero) (hg0.symm ▸ hcorner)
    exact (add_pos hA hB).ne (hinj ⟨le_rfl, (add_pos hA hB).le⟩
      ⟨(add_pos hA hB).le, le_rfl⟩ (hg0.trans (hbase.symm.trans hgT.symm)))
  have hne := m64Intrinsic_digon_terminal_velocity_ne N.metric hA hB hgeoA hgeoB hend hmeet
  have huB : N.metric.inner (alpha A) (deriv beta B : AnnulusCoordinates)
      (deriv beta B : AnnulusCoordinates) = 1 := by
    rw [← hend]
    exact hunitB B ⟨hB.le, le_rfl⟩
  apply m64Intrinsic_unit_tangents_independent N.metric (alpha A)
    (-deriv alpha A) (-deriv beta B)
  · simpa only [map_neg, neg_apply, neg_neg] using hunitA A ⟨hA.le, le_rfl⟩
  · simpa only [map_neg, neg_apply, neg_neg] using huB
  · intro he
    exact hne (neg_injective he)
  · intro he
    apply hopp
    simpa only [neg_neg] using congrArg Neg.neg he

end PoincareConjecture
