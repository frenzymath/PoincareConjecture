import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CollisionRadialExistence
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCollisionConvexCorner
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConfinedPolarInjectivity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactPolarLift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_exists_collision_continuous_polar_lift
    (N : IntrinsicAnnulus) {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a b A B r : ℝ} (hab : a < b) (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b) (hmeet : alpha A = beta B)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (horthA : N.metric.inner (intrinsicAnnulusBoundary 1 a)
      (deriv (intrinsicAnnulusBoundary 1) a) (deriv alpha 0) = 0)
    (horthB : N.metric.inner (intrinsicAnnulusBoundary 1 b)
      (deriv (intrinsicAnnulusBoundary 1) b) (deriv beta 0) = 0)
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (haInterior : ∀ t ∈ Ioc 0 A, 1 < ‖alpha t‖)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖)
    (hinwardA : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (deriv alpha 0))
    (hinwardB : 0 < inner ℝ (intrinsicAnnulusBoundary 1 b) (deriv beta 0))
    (hperiod : b - a < rampPeriod) (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ r)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfront : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
      (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta mu kappa : ℝ} (hK : N.GaussianCurvatureBound K)
    (hdelta : 0 < delta) (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hkappa : 0 < kappa) (hKkappa : K ≤ kappa ^ 2)
    (hradius : kappa * (intrinsicBoundaryLength N.metric 1 a b / 2 + max A B) < Real.pi) :
    let R := intrinsicBoundaryLength N.metric 1 a b / 2 + max A B
    ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (Omega : Set AnnulusCoordinates)
      (u : ℝ → AnnulusCoordinates),
      IsOpen Omega ∧ (0 : AnnulusCoordinates) ∈ Omega ∧ e 0 = alpha A ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega ∧
      (∀ v w : AnnulusCoordinates,
        N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
          (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w) ∧
      (∀ v ∈ Omega, ∀ w : AnnulusCoordinates,
        N.metric.pullbackCoefficients e v v w = inner ℝ v w) ∧
      (∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Omega}) ∧
      (∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega) ∧
      ContinuousOn u (Icc a b) ∧ MapsTo u (Icc a b) Omega ∧
      (∀ s ∈ Icc a b, u s ≠ 0) ∧ (∀ s ∈ Icc a b, ‖u s‖ ≤ R) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, e (t • u s) ∈ closure U) ∧
      (∀ s ∈ Icc a b, e (u s) = intrinsicAnnulusBoundary 1 s) ∧
      ‖u a‖ = A ∧ ‖u b‖ = B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, e (t • u a) = alpha (A - A * t)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, e (t • u b) = beta (B - B * t) := by
  intro R
  have hR : 0 < R := by
    have hlen := m64Intrinsic_boundaryLength_nonneg N 1 a b hab.le
    dsimp only [R]
    linarith only [hA, hlen, le_max_left A B]
  obtain ⟨e, Omega, ho, hz, _, he0, hefull, he, hm, hg, hgeo, hstar, hcontains, hex,
      ⟨vA, _, hnA, hreadA⟩, vB, _, hnB, hreadB⟩ :=
    m64Intrinsic_exists_collision_radial_vectors_with_normal_sides N ha hb hab hA hB hai hbi
      ha0 hb0 hmeet
      hsides horthA horthB hgeoA hgeoB hunitA hunitB haInterior hbInterior hinwardA hinwardB
      hperiod hshort hU hV hpV hbV hUV hcover hfV hfront hsub hK hturn harea hbudget
  obtain ⟨phi, L, hphi, hzero, _, _, hcorner⟩ :=
    m64Intrinsic_normal_collision_convex_corner N ha hb hab hA hB hai hbi ha0 hb0 hmeet
      hsides horthA horthB hgeoA hgeoB hunitA hunitB haInterior hbInterior hinwardA hinwardB
      hperiod hshort hU hV hpV hUV hcover hfV hfront hsub hK hturn harea hbudget
  have hball : closedBall (0 : AnnulusCoordinates) R ⊆ ball 0 (2 * R) := by
    intro v hv
    rw [mem_ball, dist_zero_right]
    have hn : ‖v‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hv
    linarith
  have heBall : ContinuousOn e (closedBall 0 R) :=
    (contMDiffOn_iff_contDiffOn.mp hefull).continuousOn.mono hball
  have hcontainsR (v : AnnulusCoordinates) (hvR : ‖v‖ ≤ R)
      (hconf : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) : v ∈ Omega :=
    hcontains v (hball (by simpa only [mem_closedBall, dist_zero_right] using hvR))
      (fun t ht => hsub (hconf t ht))
  have hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi / 2 := by
    have hm := mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
    linarith
  have hinj := m64Intrinsic_confined_radial_injOn N hK hsmall hkappa hKkappa hradius
    hU hV hpV hbV hUV hcover hfV.symm hsub ho hz he heBall hm hgeo hstar hcontainsR hg L
    (he0.symm ▸ hphi) (he0.symm ▸ hzero)
    (he0.symm ▸ hcorner.mono (fun _ h => h.mp))
  have hunique : ∀ p ∈ Icc a b, ∃! v : AnnulusCoordinates,
      (‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) ∧
        e v = intrinsicAnnulusBoundary 1 p := by
    intro p hp
    obtain ⟨v, _, _, hvR, hvconf, hvpoint⟩ := hex p hp
    exact ⟨v, ⟨⟨hvR, hvconf⟩, hvpoint⟩,
      fun w hw => hinj hw.1 ⟨hvR, hvconf⟩ (hw.2.trans hvpoint.symm)⟩
  obtain ⟨u, hu, huR, huconf, huboundary⟩ :=
    m64Intrinsic_exists_continuous_confined_boundary_lift heBall isClosed_closure hunique
  have identify (gamma : ℝ → AnnulusCoordinates) (T p : ℝ) (hT : 0 ≤ T) (hTR : T ≤ R)
      (hp : p ∈ Icc a b) (hgamma0 : gamma 0 = intrinsicAnnulusBoundary 1 p)
      (hgammaConf : MapsTo gamma (Icc 0 T) (closure U))
      (v : AnnulusCoordinates) (hnorm : ‖v‖ = T)
      (hread : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) = gamma (T - T * t)) :
      ‖u p‖ = T ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • u p) = gamma (T - T * t) := by
    have hvconf : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U := by
      intro t ht
      rw [hread t ht]
      exact hgammaConf ⟨by nlinarith only [ht.2, hT], by nlinarith only [ht.1, hT]⟩
    have hvpoint : e v = intrinsicAnnulusBoundary 1 p := by
      simpa only [one_smul, mul_one, sub_self, hgamma0] using hread 1 ⟨zero_le_one, le_rfl⟩
    have huv := hinj ⟨huR p hp, huconf p hp⟩
      ⟨hnorm.trans_le hTR, hvconf⟩ ((huboundary p hp).trans hvpoint.symm)
    rw [huv]
    exact ⟨hnorm, hread⟩
  have hlen := m64Intrinsic_boundaryLength_nonneg N 1 a b hab.le
  have hAR : A ≤ R := by dsimp only [R]; linarith only [hlen, le_max_left A B]
  have hBR : B ≤ R := by dsimp only [R]; linarith only [hlen, le_max_right A B]
  have hAdata := identify alpha A a hA.le hAR ⟨le_rfl, hab.le⟩ ha0
    (fun t ht => frontier_subset_closure (by rw [hfront]; exact Or.inr (Or.inl ⟨t, ht, rfl⟩)))
    vA hnA hreadA
  have hBdata := identify beta B b hB.le hBR ⟨hab.le, le_rfl⟩ hb0
    (fun t ht => frontier_subset_closure (by rw [hfront]; exact Or.inr (Or.inr ⟨t, ht, rfl⟩)))
    vB hnB hreadB
  refine ⟨e, Omega, u, ho, hz, he0, he, hm, hg, hgeo, hstar, hu,
    fun p hp => hcontainsR (u p) (huR p hp) (huconf p hp), ?_, huR, huconf, huboundary,
    hAdata.1, hBdata.1, hAdata.2, hBdata.2⟩
  intro p hp hzeroU
  obtain ⟨v, _, hvpos, hvR, hvconf, hvpoint⟩ := hex p hp
  have heq := hinj ⟨huR p hp, huconf p hp⟩ ⟨hvR, hvconf⟩
    ((huboundary p hp).trans hvpoint.symm)
  rw [← heq, hzeroU, norm_zero] at hvpos
  exact (lt_irrefl (0 : ℝ)) hvpos

end PoincareConjecture
