import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ClosedBaseGeodesics
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ContinuedPolar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_exists_collision_radial_vectors_with_normal_sides
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
    (hperiod : b - a < rampPeriod)
    (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ r)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfront : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
      (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    let R := intrinsicBoundaryLength N.metric 1 a b / 2 + max A B
    ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (Omega : Set AnnulusCoordinates),
      IsOpen Omega ∧ (0 : AnnulusCoordinates) ∈ Omega ∧
      Omega ⊆ Metric.ball 0 (2 * R) ∧ e 0 = alpha A ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e (Metric.ball 0 (2 * R)) ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega ∧
      (∀ v w : AnnulusCoordinates,
        N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
          (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w) ∧
      (∀ v ∈ Omega, ∀ w : AnnulusCoordinates,
        N.metric.pullbackCoefficients e v v w = inner ℝ v w) ∧
      (∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Omega}) ∧
      (∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega) ∧
      (∀ v ∈ Metric.ball 0 (2 * R),
        (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ standardAnnulusDomain) → v ∈ Omega) ∧
      (∀ p ∈ Icc a b, ∃ v : AnnulusCoordinates, v ∈ Omega ∧ 0 < ‖v‖ ∧ ‖v‖ ≤ R ∧
        (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) ∧
        e v = intrinsicAnnulusBoundary 1 p) ∧
      (∃ v : AnnulusCoordinates, v ∈ Omega ∧ ‖v‖ = A ∧
        ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) = alpha (A - A * t)) ∧
      ∃ v : AnnulusCoordinates, v ∈ Omega ∧ ‖v‖ = B ∧
        ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) = beta (B - B * t) := by
  intro R
  have hlength := m64Intrinsic_boundaryLength_nonneg N 1 a b hab.le
  have hAR : A ≤ R := by
    dsimp only [R]
    linarith only [hlength, le_max_left A B]
  have hBR : B ≤ R := by
    dsimp only [R]
    linarith only [hlength, le_max_right A B]
  have hR : 0 < R := hA.trans_le hAR
  have hsideA : MapsTo alpha (Icc 0 A) (closure U) := by
    intro t ht
    apply frontier_subset_closure
    rw [hfront]
    exact Or.inr (Or.inl (mem_image_of_mem alpha ht))
  have hsideB : MapsTo beta (Icc 0 B) (closure U) := by
    intro t ht
    apply frontier_subset_closure
    rw [hfront]
    exact Or.inr (Or.inr (mem_image_of_mem beta ht))
  have hinterior : ∀ p ∈ Ioo a b, ∃ (eta : ℝ → AnnulusCoordinates) (T : ℝ),
      0 < T ∧ T ≤ R ∧ ContDiff ℝ ∞ eta ∧
      eta 0 = intrinsicAnnulusBoundary 1 p ∧ eta T = alpha A ∧
      MapsTo eta (Icc 0 T) (closure U) ∧ InjOn eta (Icc 0 T) ∧
      N.metric.IsGeodesicOn eta (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, N.metric.inner (eta t) (deriv eta t) (deriv eta t) = 1 := by
    intro p hp
    obtain ⟨eta, T, hT, hTR, he, he0, heT, heconf, _, hei, hegeo, heunit⟩ :=
      m64Intrinsic_exists_short_collision_geodesic N ha hb hab hA hB hp hai hbi
        ha0 hb0 hmeet hsides horthA horthB hgeoA hgeoB hunitA hunitB
        haInterior hbInterior hinwardA hinwardB hperiod hshort
        hU hV hpV hbV hUV hcover hfV hfront hsub hK hturn harea hbudget
    exact ⟨eta, T, hT, hTR, he, he0, heT, heconf, hei, hegeo, heunit⟩
  have hpaths := m64Intrinsic_closed_base_vertex_geodesics N ha hb hA hB hAR hBR hai hbi
    ha0 hb0 hmeet hgeoA hgeoB hunitA hunitB hsideA hsideB hinterior
  have hvertex := hsub (hsideA (right_mem_Icc.mpr hA.le))
  obtain ⟨e, Omega, ho, hz, hball, he0, hefull, he, hm, hg, hgeo, hstar, hcontains,
      hrealize⟩ := m64Intrinsic_exists_continued_radial_exponential_realizing_geodesics
        N hvertex (show 0 < 2 * R from by linarith)
  have normal (gamma : ℝ → AnnulusCoordinates) (T : ℝ) (hT : 0 < T) (hTR : T ≤ R)
      (hgamma : ContDiff ℝ ∞ gamma) (hi : InjOn gamma (Icc 0 T))
      (hend : gamma T = alpha A) (hconf : MapsTo gamma (Icc 0 T) (closure U))
      (hgg : N.metric.IsGeodesicOn gamma (Icc 0 T))
      (hgu : ∀ t ∈ Icc 0 T, N.metric.inner (gamma t) (deriv gamma t) (deriv gamma t) = 1) :
      ∃ v : AnnulusCoordinates, v ∈ Omega ∧ ‖v‖ = T ∧
        ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) = gamma (T - T * t) := by
    obtain ⟨hq, hq0, _, _, _, hqg, hqu⟩ :=
      m64Intrinsic_reverse_closed_unit_geodesic N.metric hgamma hi hgg hgu
    exact hrealize (fun t => gamma (T - t)) hq T hT (by linarith)
      (hq0.trans hend) hqg (fun t ht => hsub (hconf ⟨by linarith [ht.2], by linarith [ht.1]⟩))
      (hqu 0 ⟨le_rfl, hT.le⟩)
  refine ⟨e, Omega, ho, hz, hball, he0, hefull, he, hm, hg, hgeo, hstar, hcontains, ?_,
    normal alpha A hA hAR ha hai rfl hsideA hgeoA hunitA,
    normal beta B hB hBR hb hbi hmeet.symm hsideB hgeoB hunitB⟩
  intro p hp
  obtain ⟨q, T, hT, hTR, hq, hq0, hqT, hqconf, _, hqgeo, hqunit⟩ := hpaths p hp
  obtain ⟨v, hv, hnorm, hreadout⟩ := hrealize q hq T hT (by linarith) hq0 hqgeo
    (fun t ht => hsub (hqconf ht)) (hqunit 0 ⟨le_rfl, hT.le⟩)
  refine ⟨v, hv, by rwa [hnorm], by rwa [hnorm], ?_, ?_⟩
  · intro t ht
    rw [hreadout t ht]
    exact hqconf ⟨mul_nonneg hT.le ht.1,
      (mul_le_mul_of_nonneg_left ht.2 hT.le).trans_eq (mul_one T)⟩
  · simpa only [one_smul, mul_one, hqT] using hreadout 1 (by norm_num)

theorem m64Intrinsic_exists_collision_radial_vectors
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
    (hperiod : b - a < rampPeriod)
    (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ r)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfront : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
      (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    let R := intrinsicBoundaryLength N.metric 1 a b / 2 + max A B
    ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (Omega : Set AnnulusCoordinates),
      IsOpen Omega ∧ (0 : AnnulusCoordinates) ∈ Omega ∧
      Omega ⊆ Metric.ball 0 (2 * R) ∧ e 0 = alpha A ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e (Metric.ball 0 (2 * R)) ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega ∧
      (∀ v w : AnnulusCoordinates,
        N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
          (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w) ∧
      (∀ v ∈ Omega, ∀ w : AnnulusCoordinates,
        N.metric.pullbackCoefficients e v v w = inner ℝ v w) ∧
      (∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Omega}) ∧
      (∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega) ∧
      (∀ v ∈ Metric.ball 0 (2 * R),
        (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ standardAnnulusDomain) → v ∈ Omega) ∧
      ∀ p ∈ Icc a b, ∃ v : AnnulusCoordinates, v ∈ Omega ∧ 0 < ‖v‖ ∧ ‖v‖ ≤ R ∧
        (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) ∧
        e v = intrinsicAnnulusBoundary 1 p := by
  obtain ⟨e, Omega, ho, hz, hball, he0, hefull, he, hm, hg, hgeo, hstar, hcontains, hex, _, _⟩ :=
    m64Intrinsic_exists_collision_radial_vectors_with_normal_sides N ha hb hab hA hB hai hbi
      ha0 hb0 hmeet hsides horthA horthB hgeoA hgeoB hunitA hunitB haInterior hbInterior
      hinwardA hinwardB hperiod hshort hU hV hpV hbV hUV hcover hfV hfront hsub
      hK hturn harea hbudget
  exact ⟨e, Omega, ho, hz, hball, he0, hefull, he, hm, hg, hgeo, hstar, hcontains, hex⟩

end PoincareConjecture
