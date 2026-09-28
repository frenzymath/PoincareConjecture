import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonTerminalTangents
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonConvexity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedDigonRegion





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture






theorem m64Intrinsic_confined_digon_convex_coordinates
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
    ∃ W Y : Set AnnulusCoordinates,
      IsOpen W ∧ IsOpen Y ∧ IsPathConnected W ∧ IsPathConnected Y ∧
      Bornology.IsBounded W ∧ ¬ Bornology.IsBounded Y ∧ Disjoint W Y ∧
      W ∪ Y = (frontier W)ᶜ ∧
      frontier W = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∧ frontier Y = frontier W ∧
      IsCompact (closure W) ∧ W ⊆ U ∧ closure W ⊆ closure U ∧
      (N.metric.cornerAngle (alpha 0) (deriv alpha 0) (deriv beta 0) +
        N.metric.cornerAngle (alpha A) (-deriv alpha A) (-deriv beta B) ≤
          max K 0 * intrinsicAnnulusArea N.metric) ∧
      (∃ (phi0 : AnnulusCoordinates → ℝ × ℝ)
          (L0 : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
        HasFDerivAt phi0 L0.toContinuousLinearMap (alpha 0) ∧ phi0 (alpha 0) = 0 ∧
        L0.symm (1, 0) = deriv alpha 0 ∧ L0.symm (0, 1) = deriv beta 0 ∧
        (∀ᶠ z in 𝓝 (alpha 0), z ∈ closure W ↔ 0 ≤ (phi0 z).1 ∧ 0 ≤ (phi0 z).2)) ∧
      ∃ (phi1 : AnnulusCoordinates → ℝ × ℝ)
        (L1 : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
        HasFDerivAt phi1 L1.toContinuousLinearMap (alpha A) ∧ phi1 (alpha A) = 0 ∧
        L1.symm (1, 0) = -deriv alpha A ∧ L1.symm (0, 1) = -deriv beta B ∧
        (∀ᶠ z in 𝓝 (alpha A), z ∈ closure W ↔ 0 ≤ (phi1 z).1 ∧ 0 ≤ (phi1 z).2) := by
  have hai := m64Intrinsic_closed_corner_ray_injOn N hK hsmall hU hV hpV hbV hUV
    hcover hfront hsub ha hgeoA hunitA hconfA L hphi hzero hcorner
  have hbi := m64Intrinsic_closed_corner_ray_injOn N hK hsmall hU hV hpV hbV hUV
    hcover hfront hsub hb hgeoB hunitB hconfB L
      (hbase.symm ▸ hphi) (hbase.symm ▸ hzero) (hbase.symm ▸ hcorner)
  have hind0 := m64Intrinsic_digon_initial_transverse_at_convex_corner N.metric ha hb
    hA hB hgeoA hgeoB hbase hmeet (hunitA 0 ⟨le_rfl, hA.le⟩)
      (hunitB 0 ⟨le_rfl, hB.le⟩) (hconfA.mono_left Ioo_subset_Icc_self)
      (hconfB.mono_left Ioo_subset_Icc_self) L hphi hzero hcorner
  have hind1 := m64Intrinsic_digon_terminal_transverse_at_convex_corner N hK hsmall
    hU hV hpV hbV hUV hcover hfront hsub ha hb hA hB hgeoA hgeoB hbase hend hmeet
      hunitA hunitB hconfA hconfB L hphi hzero hcorner
  obtain ⟨W, Y, hW, hY, hpW, hpY, hbW, hbY, hWY, hcW, hfW, hfY,
      hkW, hWU, hclWU, hclcover⟩ := m64Intrinsic_exists_nested_digon_region
    hU hV hpV hbV hUV hcover hfront hA hB ha.continuous.continuousOn
      hb.continuous.continuousOn hai hbi hbase hend hmeet hconfA hconfB
  have hconvex := m64Intrinsic_small_digon_convex_coordinates N ha hb hA hB hai hbi
    hbase hend hmeet hgeoA hgeoB hunitA hunitB hind0 hind1 hW hY hWY hfW hfY
      hclcover hpY.isConnected.isPreconnected (hclWU.trans hsub) hK hsmall
  exact ⟨W, Y, hW, hY, hpW, hpY, hbW, hbY, hWY, hcW, hfW, hfY, hkW,
    hWU, hclWU, hconvex⟩

end PoincareConjecture
