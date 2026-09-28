import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonRegionCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonCornerCoordinates
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionCurvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_small_digon_convex_coordinates
    (N : IntrinsicAnnulus) {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (hind0 : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi) :
    N.metric.cornerAngle (alpha 0) (deriv alpha 0) (deriv beta 0) +
        N.metric.cornerAngle (alpha A) (-deriv alpha A) (-deriv beta B) ≤
      max K 0 * intrinsicAnnulusArea N.metric ∧
    (∃ (phi : AnnulusCoordinates → ℝ × ℝ)
        (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha 0) ∧ phi (alpha 0) = 0 ∧
      L.symm (1, 0) = deriv alpha 0 ∧ L.symm (0, 1) = deriv beta 0 ∧
      (∀ᶠ z in 𝓝 (alpha 0), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2)) ∧
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha A) ∧ phi (alpha A) = 0 ∧
      L.symm (1, 0) = -deriv alpha A ∧ L.symm (0, 1) = -deriv beta B ∧
      (∀ᶠ z in 𝓝 (alpha A), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) := by
  have hregA (t : ℝ) (ht : t ∈ Ioo 0 A) : deriv alpha t ≠ 0 := by
    intro hz
    have hu := hunitA t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hregB (t : ℝ) (ht : t ∈ Ioo 0 B) : deriv beta t ≠ 0 := by
    intro hz
    have hu := hunitB t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hcompact : IsCompact (closure U) :=
    m64Intrinsic_standardAnnulus_isCompact.of_isClosed_subset isClosed_closure hsub
  obtain ⟨R, v0, v1, hv0, hv1⟩ := m64Intrinsic_exists_digon_triangulation
    ha hb hA hB hai hbi hregA hregB hbase hend hmeet hind0 hind1
    hU hV hUV hfront hfV hcompact
  have hangle := m64Intrinsic_digon_angle_sum_le_curvature N R ha hb hA hB hai hbi
    hbase hend hmeet hgeoA hgeoB hunitA hunitB hU hV hUV hfront hfV
    hclosure hVconn v0 v1 hv0 hv1
  have hbound := hangle.trans
    (m64Intrinsic_region_gaussian_integral_le_area N hK hcompact hsub)
  have hn0 := m64Intrinsic_coordinate_vertex_angle_nonneg
    N.metric R.coordinates R.basis v0.1
  have hn1 := m64Intrinsic_coordinate_vertex_angle_nonneg
    N.metric R.coordinates R.basis v1.1
  have hsmall0 : coordinateVertexAngleContribution N.metric R.coordinates R.basis v0.1 <
      Real.pi := by linarith only [hbound, hn1, hsmall]
  have hsmall1 : coordinateVertexAngleContribution N.metric R.coordinates R.basis v1.1 <
      Real.pi := by linarith only [hbound, hn0, hsmall]
  obtain ⟨phi0, L0, hd0, hz0, haL0, hbL0, hr0, hf0⟩ :=
    m64Intrinsic_digon_initial_convex_coordinates R N.metric ha hb hA hB hai hbi
      hbase hind0 hU hV hUV hfront hfV v0 hv0 hsmall0
  obtain ⟨phi1, L1, hd1, hz1, haL1, hbL1, hr1, hf1⟩ :=
    m64Intrinsic_digon_terminal_convex_coordinates R N.metric ha hb hA hB hai hbi
      hend hind1 hU hV hUV hfront hfV v1 hv1 hsmall1
  refine ⟨?_, ⟨phi0, L0, hd0, hz0, haL0, hbL0, hr0⟩,
    phi1, L1, hd1, hz1, haL1, hbL1, hr1⟩
  rwa [hf0, hf1] at hbound

end PoincareConjecture
