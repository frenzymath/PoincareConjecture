import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ShortCollisionGeodesic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_reverse_closed_unit_geodesic
    (G : RiemannianMetric 2 AnnulusCoordinates) {eta : ℝ → AnnulusCoordinates}
    (he : ContDiff ℝ ∞ eta) {T : ℝ} (hi : InjOn eta (Icc 0 T))
    (hgeo : G.IsGeodesicOn eta (Icc 0 T))
    (hunit : ∀ t ∈ Icc 0 T, G.inner (eta t) (deriv eta t) (deriv eta t) = 1) :
    let q := fun t : ℝ => eta (T - t)
    ContDiff ℝ ∞ q ∧ q 0 = eta T ∧ q T = eta 0 ∧
      q '' Icc 0 T = eta '' Icc 0 T ∧ InjOn q (Icc 0 T) ∧
      G.IsGeodesicOn q (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, G.inner (q t) (deriv q t) (deriv q t) = 1 := by
  intro q
  have htmap (t : ℝ) (ht : t ∈ Icc 0 T) : T - t ∈ Icc 0 T :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hderiv (t : ℝ) : deriv q t = -deriv eta (T - t) :=
    deriv_comp_const_sub eta T t
  refine ⟨he.comp (by fun_prop), by simp [q], by simp [q], ?_, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨T - t, htmap t ht, rfl⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨T - t, htmap t ht, by simp only [q, sub_sub_cancel]⟩
  · intro s hs t ht hst
    have h := hi (htmap s hs) (htmap t ht) hst
    linarith
  · have h := hgeo.comp_affine (-1) T
    intro t ht
    convert h t (show -1 * t + T ∈ Icc 0 T from
      ⟨by linarith [ht.2], by linarith [ht.1]⟩) using 1
    simp only [q, neg_one_mul, sub_eq_add_neg, add_comm]
  · intro t ht
    change G.inner (eta (T - t)) (deriv q t) (deriv q t) = 1
    simp only [hderiv, map_neg, neg_apply, neg_neg]
    exact hunit (T - t) (htmap t ht)

theorem m64Intrinsic_closed_base_vertex_geodesics
    (N : IntrinsicAnnulus) {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a b A B R : ℝ} (hA : 0 < A) (hB : 0 < B) (hAR : A ≤ R) (hBR : B ≤ R)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b) (hmeet : alpha A = beta B)
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    {K : Set AnnulusCoordinates} (hconfA : MapsTo alpha (Icc 0 A) K)
    (hconfB : MapsTo beta (Icc 0 B) K)
    (hinterior : ∀ p ∈ Ioo a b, ∃ (eta : ℝ → AnnulusCoordinates) (T : ℝ),
      0 < T ∧ T ≤ R ∧ ContDiff ℝ ∞ eta ∧
      eta 0 = intrinsicAnnulusBoundary 1 p ∧ eta T = alpha A ∧
      MapsTo eta (Icc 0 T) K ∧ InjOn eta (Icc 0 T) ∧
      N.metric.IsGeodesicOn eta (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, N.metric.inner (eta t) (deriv eta t) (deriv eta t) = 1) :
    ∀ p ∈ Icc a b, ∃ (q : ℝ → AnnulusCoordinates) (T : ℝ),
      0 < T ∧ T ≤ R ∧ ContDiff ℝ ∞ q ∧ q 0 = alpha A ∧
      q T = intrinsicAnnulusBoundary 1 p ∧ MapsTo q (Icc 0 T) K ∧
      InjOn q (Icc 0 T) ∧ N.metric.IsGeodesicOn q (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, N.metric.inner (q t) (deriv q t) (deriv q t) = 1 := by
  intro p hp
  have hsource : ∃ (eta : ℝ → AnnulusCoordinates) (T : ℝ),
      0 < T ∧ T ≤ R ∧ ContDiff ℝ ∞ eta ∧
      eta 0 = intrinsicAnnulusBoundary 1 p ∧ eta T = alpha A ∧
      MapsTo eta (Icc 0 T) K ∧ InjOn eta (Icc 0 T) ∧
      N.metric.IsGeodesicOn eta (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, N.metric.inner (eta t) (deriv eta t) (deriv eta t) = 1 := by
    by_cases hpa : p = a
    · subst p
      exact ⟨alpha, A, hA, hAR, ha, ha0, rfl, hconfA, hai, hgeoA, hunitA⟩
    by_cases hpb : p = b
    · subst p
      exact ⟨beta, B, hB, hBR, hb, hb0, hmeet.symm, hconfB, hbi, hgeoB, hunitB⟩
    exact hinterior p ⟨lt_of_le_of_ne hp.1 (Ne.symm hpa), lt_of_le_of_ne hp.2 hpb⟩
  obtain ⟨eta, T, hT, hTR, he, he0, heT, hconf, hi, hgeo, hunit⟩ := hsource
  obtain ⟨hq, hq0, hqT, himage, hqi, hqgeo, hqunit⟩ :=
    m64Intrinsic_reverse_closed_unit_geodesic N.metric he hi hgeo hunit
  refine ⟨fun t => eta (T - t), T, hT, hTR, hq, hq0.trans heT,
    hqT.trans he0, ?_, hqi, hqgeo, hqunit⟩
  exact mapsTo_iff_image_subset.mpr
    (himage ▸ mapsTo_iff_image_subset.mp hconf)

end PoincareConjecture
