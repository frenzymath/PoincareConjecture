import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleAngleBound
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleTerminalCorner
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionCurvature





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_small_triangle_terminal_convex_coordinates
    (N : IntrinsicAnnulus)
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (hci : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hbi : InjOn beta (Icc 0 B))
    (hcreg : ∀ t ∈ Icc 0 D, deriv base t ≠ 0)
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (horth0 : N.metric.inner (base 0) (deriv base 0) (deriv alpha 0) = 0)
    (horth1 : N.metric.inner (base D) (deriv base D) (deriv beta 0) = 0)
    (hageo : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hbgeo : N.metric.IsGeodesicOn beta (Icc 0 B))
    (haunit : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hbunit : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (hindT : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {a b : ℝ} (habound : a ≤ b)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    (hcircle : base '' Icc 0 D = intrinsicAnnulusBoundary 1 '' Icc a b)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward0 : 0 < inner ℝ (base 0) (deriv alpha 0))
    (hinward1 : 0 < inner ℝ (base D) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K : ℝ} (hK : N.GaussianCurvatureBound K)
    (hbudget : max K 0 * intrinsicAnnulusArea N.metric +
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b < Real.pi) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha A) ∧ phi (alpha A) = 0 ∧
      L.symm (1, 0) = -deriv alpha A ∧ L.symm (0, 1) = -deriv beta B ∧
      (∀ᶠ z in 𝓝 (alpha A), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) := by
  have hareg (t : ℝ) (ht : t ∈ Icc 0 A) : deriv alpha t ≠ 0 := by
    intro hz
    have hu := haunit t ht
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hbreg (t : ℝ) (ht : t ∈ Icc 0 B) : deriv beta t ≠ 0 := by
    intro hz
    have hu := hbunit t ht
    simp only [hz, map_zero] at hu
    norm_num at hu
  have orth_independent (p u v : AnnulusCoordinates) (hu : u ≠ 0) (hv : v ≠ 0)
      (ho : N.metric.inner p u v = 0) :
      LinearIndependent ℝ (![u, v] : Fin 2 → AnnulusCoordinates) := by
    rw [linearIndependent_fin2]
    refine ⟨hv, ?_⟩
    intro c he
    change c • v = u at he
    have hpos := N.metric.pos p v hv
    rw [← he, map_smul, smul_apply, smul_eq_mul] at ho
    have hc0 : c = 0 := (mul_eq_zero.mp ho).resolve_right hpos.ne'
    apply hu
    simpa only [hc0, zero_smul] using he.symm
  have hindA := orth_independent (base 0) (deriv base 0) (deriv alpha 0)
    (hcreg 0 ⟨le_rfl, hD.le⟩) (hareg 0 ⟨le_rfl, hA.le⟩) horth0
  have hindB := orth_independent (base D) (-deriv base D) (deriv beta 0)
    (neg_ne_zero.mpr (hcreg D ⟨hD.le, le_rfl⟩)) (hbreg 0 ⟨le_rfl, hB.le⟩)
    (by rw [map_neg, neg_apply, horth1, neg_zero])
  have hcompact : IsCompact (closure U) :=
    m64Intrinsic_standardAnnulus_isCompact.of_isClosed_subset isClosed_closure hsub
  obtain ⟨R, v0, v1, vT, hv0, hv1, hvT⟩ := m64Intrinsic_exists_triangle_region_triangulation
    hc ha hb hD hA hB hci hai hbi
    (fun t ht => hcreg t (Ioo_subset_Icc_self ht))
    (fun t ht => hareg t (Ioo_subset_Icc_self ht))
    (fun t ht => hbreg t (Ioo_subset_Icc_self ht)) hstartA hstartB hmeet
    hbaseA hbaseB hsides hindA hindB hindT hU hV hUV hfront hfV hcompact
  have hangle := m64Intrinsic_triangle_region_angle_le_original_turning N R hc ha hb
    hD hA hB hci hai hbi (fun t ht => hcreg t (Ioo_subset_Icc_self ht))
    hstartA hstartB hmeet hbaseA hbaseB hsides
    (hcreg 0 ⟨le_rfl, hD.le⟩) (hcreg D ⟨hD.le, le_rfl⟩) horth0 horth1
    hageo hbgeo haunit hbunit habound hcircleInj hcircle hU hV hUV hfront hfV
    hclosure hVconn hinward0 hinward1 hsub v0 v1 vT hv0 hv1 hvT
  have hcurvature := m64Intrinsic_region_gaussian_integral_le_area N hK hcompact hsub
  have hsmall : coordinateVertexAngleContribution N.metric R.coordinates R.basis vT.1 <
      Real.pi := by linarith only [hangle, hcurvature, hbudget]
  exact m64Intrinsic_triangle_terminal_convex_coordinates R N.metric hc ha hb hA hB
    hai hbi hmeet hbaseA hindT hU hV hUV hfront hfV vT hvT hsmall

end PoincareConjecture
