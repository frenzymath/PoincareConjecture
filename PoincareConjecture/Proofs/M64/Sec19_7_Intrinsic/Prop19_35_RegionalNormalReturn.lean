import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CentralRegionalDescent
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RawInnerNormalReturn

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_no_regional_normal_return
    (N : IntrinsicAnnulus) {K delta r q mu alpha h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hh : 0 < h) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / q ≤ alpha)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {x y T : ℝ} (hT : 0 < T) (hTh : T ≤ h) (hgi : InjOn gamma (Icc 0 T))
    (h0 : gamma 0 = intrinsicAnnulusBoundary 1 x)
    (h1 : gamma T = intrinsicAnnulusBoundary 1 y)
    (hinside : ∀ t ∈ Ioo 0 T, 1 < ‖gamma t‖)
    (hgeo : N.metric.IsGeodesicOn gamma (Icc 0 T))
    (hunit : N.metric.inner (gamma 0) (deriv gamma 0) (deriv gamma 0) = 1)
    (horth : N.metric.inner (intrinsicAnnulusBoundary 1 x)
      (deriv (intrinsicAnnulusBoundary 1) x) (deriv gamma 0) = 0)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 x) (deriv gamma 0))
    (hterminal : LinearIndependent ℝ
      (![deriv (intrinsicAnnulusBoundary 1) y, deriv gamma T] : Fin 2 → AnnulusCoordinates))
    (hperiod : |y - x| < rampPeriod)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc (min x y) (max x y) ∪
      gamma '' Icc 0 T)
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates) (height : ℝ → ℝ)
    (hbase : ∀ p, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hunit0 : ∀ p, N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    (horth0 : ∀ p, N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0)
    (hinward0 : ∀ p, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hAnn : ∀ p, 0 < height p ∧
      (height p = h ∨ ‖e !₂[p, height p]‖ = 1 ∨ ‖e !₂[p, height p]‖ = 2))
    (hgeodesic : ∀ p, N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (height p)))
    (hmetric : ∀ p, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) : False := by
  by_cases hshort : intrinsicBoundaryLength N.metric 1 (min x y) (max x y) ≤ r
  · have hclosed : closure U ∪ closure V = univ := by
      apply eq_univ_of_forall
      intro p
      by_cases hp : p ∈ frontier U
      · exact Or.inl (frontier_subset_closure hp)
      · have hp' : p ∈ U ∪ V := by simpa only [hcover, mem_compl_iff] using hp
        exact hp'.elim (fun h => Or.inl (subset_closure h))
          (fun h => Or.inr (subset_closure h))
    exact m64Intrinsic_no_short_transverse_inner_return N hg hT hgi h0 h1 hinside
      hgeo hunit horth hinward hterminal hperiod hU hV hUV hfU hfront.symm hclosed hpV
      hsub hK hturn harea hbudget hshort
  have hxy : x ≠ y := by
    intro hxy
    have hpoints : gamma 0 = gamma T := by rw [h0, h1, hxy]
    exact hT.ne (hgi ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hpoints)
  have hends :
      (gamma 0 = intrinsicAnnulusBoundary 1 (min x y) ∧
        gamma T = intrinsicAnnulusBoundary 1 (max x y)) ∨
      (gamma 0 = intrinsicAnnulusBoundary 1 (max x y) ∧
        gamma T = intrinsicAnnulusBoundary 1 (min x y)) := by
    rcases le_total x y with hxy | hxy
    · rw [min_eq_left hxy, max_eq_right hxy]
      exact Or.inl ⟨h0, h1⟩
    · rw [min_eq_right hxy, max_eq_left hxy]
      exact Or.inr ⟨h0, h1⟩
  exact m64Intrinsic_no_central_regional_return N hK hdelta hdeltaSmall hq hqr hh hhq
    hturn halpha harea hbudget hmodel hareaLoss hU hV hpV hbV hUV hcover hfront hsub
    (min_lt_max.mpr hxy) (by simpa only [max_sub_min_eq_abs] using hperiod)
    (lt_of_not_ge hshort) hg hT hTh hgi hends hinside hgeo hunit hfU e he normal height
    (fun p _ => hbase p) (fun p _ => hderiv p) (fun p _ => hunit0 p)
    (fun p _ => horth0 p) (fun p _ => hinward0 p) (fun p _ => hAnn p)
    (fun p _ => hgeodesic p) (fun p _ => hmetric p)

end PoincareConjecture
