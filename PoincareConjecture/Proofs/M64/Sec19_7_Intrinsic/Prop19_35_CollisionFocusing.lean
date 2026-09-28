import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CollisionPolarLift
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalPolarEndpoint
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ContinuousFocusingArc
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingLoss

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_normal_collision_focusing
    (N : IntrinsicAnnulus) {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a b A B r rho : ℝ} (hab : a < b) (hA : 0 < A) (hB : 0 < B)
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
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hdelta : 0 < delta) (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hradius : intrinsicBoundaryLength N.metric 1 a b / 2 + max A B ≤ rho)
    (hangle : Real.sqrt (max K 1) * rho ≤ Real.pi / 4) :
    (Real.cos (Real.sqrt (max K 1) * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
      (Real.sin (Real.sqrt (max K 1) * rho) / Real.sqrt (max K 1)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) ∧
    intrinsicBoundaryLength N.metric 1 a b ≤
      2 * rho * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  have hkappa : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_right K 1))
  have hKkappa : K ≤ Real.sqrt (max K 1) ^ 2 := by
    rw [Real.sq_sqrt (zero_le_one.trans (le_max_right K 1))]
    exact le_max_left K 1
  have hRpi : Real.sqrt (max K 1) *
      (intrinsicBoundaryLength N.metric 1 a b / 2 + max A B) < Real.pi :=
    ((mul_le_mul_of_nonneg_left hradius hkappa.le).trans hangle).trans_lt
      (by linarith [Real.pi_pos])
  obtain ⟨e, Omega, u, ho, hz, _, he, hm, hg, hgeo, hstar, hu, humap, hune, huR,
      huconf, huboundary, _, _, huA, huB⟩ :=
    m64Intrinsic_exists_collision_continuous_polar_lift N ha hb hab hA hB hai hbi ha0 hb0 hmeet
      hsides horthA horthB hgeoA hgeoB hunitA hunitB haInterior hbInterior hinwardA hinwardB
      hperiod hshort hU hV hpV hbV hUV hcover hfV hfront hsub hK hdelta hturn harea hbudget
      hkappa hKkappa hRpi
  have hsharp : Real.cos (Real.sqrt (max K 1) * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
      (Real.sin (Real.sqrt (max K 1) * rho) / Real.sqrt (max K 1)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
    apply m64Intrinsic_continuous_focusing_arc_length_le_turning N K hK ho hz he hgeo hm hg hstar
      hangle hab.le hu humap huboundary hune (fun s hs => (huR s hs).trans hradius)
      (fun s hs t ht => hsub (huconf s hs t (Ioo_subset_Icc_self ht)))
    · exact m64Intrinsic_normal_polar_endpoint_orthogonal N
        (((contMDiffOn_iff_contDiffOn.mp he).contDiffAt
          (ho.mem_nhds (humap ⟨le_rfl, hab.le⟩))).differentiableAt (by simp))
        (ha.differentiable (by simp) 0) huA horthA _
    · exact m64Intrinsic_normal_polar_endpoint_orthogonal N
        (((contMDiffOn_iff_contDiffOn.mp he).contDiffAt
          (ho.mem_nhds (humap ⟨hab.le, le_rfl⟩))).differentiableAt (by simp))
        (hb.differentiable (by simp) 0) huB horthB _
  have hlen := m64Intrinsic_boundaryLength_nonneg N 1 a b hab.le
  have hrho : 0 < rho := by linarith only [hA, hlen, le_max_left A B, hradius]
  exact ⟨hsharp, m64Intrinsic_sine_focusing_length_le_twice_radius_turning hrho hkappa hangle
    hlen (m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 a b hab.le) hsharp⟩

end PoincareConjecture
