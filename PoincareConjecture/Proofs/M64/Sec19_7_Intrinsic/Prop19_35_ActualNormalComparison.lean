import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GlobalRayEmbedding
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseInnerEndpoint
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseRetainedBases
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CyclicRetainedComparisonAE

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_comparison_of_actual_normal_geometry
    (N : IntrinsicAnnulus) {K delta r q mu alpha h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hh : 0 < h) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / q ≤ alpha)
    (hsmall : 4 * (q / 10) * alpha < 1)
    (hrhoSmall : q / 10 ≤ 3 * q / (1600 * delta))
    (hfirst : 2 * q < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates) (height : ℝ → ℝ) (hheight : Measurable height)
    (hbase : ∀ p, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hunit0 : ∀ p, N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    (horth0 : ∀ p, N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0)
    (hinward0 : ∀ p, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hAnn : ∀ p, 0 < height p ∧
      (height p = h ∨ ‖e !₂[p, height p]‖ = 1 ∨ ‖e !₂[p, height p]‖ = 2))
    (hcap : ∀ p, height p ≤ h)
    (hinterior : ∀ p, ∀ t ∈ Ioo 0 (height p), 1 < ‖e !₂[p, t]‖ ∧ ‖e !₂[p, t]‖ < 2)
    (himage : ∀ p, ∀ t ∈ Icc 0 (height p), e !₂[p, t] ∈ standardAnnulusDomain)
    (hgeodesic : ∀ p, N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (height p)))
    (hmetric : ∀ p, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) :
    (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod <
      intrinsicBoundaryLength N.metric 2 0 rampPeriod := by
  classical
  have hdelta1 : delta < 1 := hdeltaSmall.trans (by norm_num)
  have hray (p : ℝ) (hp : intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha) :
      InjOn (fun t => e !₂[p, t]) (Icc 0 (height p)) :=
    m64Intrinsic_good_normal_ray_injOn N hK hdelta hdeltaSmall hq hqr hhq hturn halpha
      hsmall hfirst harea hbudget hmodel hareaLoss e he normal height hbase hderiv
      hunit0 horth0 hinward0 hAnn hcap hinterior hgeodesic hmetric hp
  obtain ⟨Good, hGood, _, hGoodAE, _, _, htransverse⟩ :=
    m64Intrinsic_exists_transverse_retained_bases e he
      (m64Intrinsic_contDiff_boundary 1) MeasurableSet.univ
  have hinner (p : ℝ) (hp : p ∈ Ico (0 : ℝ) rampPeriod)
      (hk : intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha)
      (hg : p ∈ Good) : ‖e !₂[p, height p]‖ ≠ 1 :=
    m64Intrinsic_no_transverse_inner_endpoint N hK hdelta hdeltaSmall hq hqr hh hhq
      hturn halpha harea hbudget hmodel hareaLoss e he normal height hbase hderiv
      hunit0 horth0 hinward0 hAnn hgeodesic hmetric hp hk (hcap p) (hinterior p)
      (hray p hk) (htransverse p hg)
  let H : ℝ → ℝ := Good.piecewise height 0
  have hH : Measurable H := hheight.piecewise hGood measurable_const
  have hHnonneg (p : ℝ) : 0 ≤ H p := by
    by_cases hp : p ∈ Good <;> simp only [H, piecewise, hp, ite_true, ite_false,
      Pi.zero_apply]
    · exact (hAnn p).1.le
    · exact le_rfl
  have hHheight (p : ℝ) : H p ≤ height p := by
    by_cases hp : p ∈ Good <;> simp only [H, piecewise, hp, ite_true, ite_false,
      Pi.zero_apply]
    · exact le_rfl
    · exact (hAnn p).1.le
  have hHinside (p : ℝ) (hp : p ∈ Ico (0 : ℝ) rampPeriod)
      (hk : intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha) :
      ∀ t ∈ Ioc 0 (H p), 1 < ‖e !₂[p, t]‖ ∧ ‖e !₂[p, t]‖ ≤ 2 := by
    intro t ht
    have hg : p ∈ Good := by
      by_contra hn
      have hzero : H p = 0 := by simp only [H, piecewise, hn, ite_false, Pi.zero_apply]
      linarith only [ht.1, ht.2, hzero]
    have htbound : t ≤ height p := ht.2.trans (hHheight p)
    rcases lt_or_eq_of_le htbound with hlt | heq
    · exact ⟨(hinterior p t ⟨ht.1, hlt⟩).1, (hinterior p t ⟨ht.1, hlt⟩).2.le⟩
    · subst t
      have hi := himage p (height p) ⟨(hAnn p).1.le, le_rfl⟩
      exact ⟨lt_of_le_of_ne hi.1 (Ne.symm (hinner p hp hk hg)), hi.2⟩
  have heta (x : AnnulusCoordinates) : !₂[x 0, x 1] = x := by
    ext i
    fin_cases i <;> rfl
  have hmetric' (x : AnnulusCoordinates)
      (hxk : intrinsicGeodesicCurvature N.metric N.connection 1 (x 0) ≤ alpha)
      (hxt : x 1 ∈ Icc 0 (H (x 0))) (v : AnnulusCoordinates) :
      (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v)
          (mfderiv (𝓡 2) (𝓡 2) e x v) := by
    have hm := hmetric (x 0) hxk (x 1) ⟨hxt.1, hxt.2.trans (hHheight (x 0))⟩ v
    change (1 - delta) ^ 2 *
        (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
      N.metric.euclideanCoefficients (e !₂[x 0, x 1])
        (fderiv ℝ e !₂[x 0, x 1] v) (fderiv ℝ e !₂[x 0, x 1] v) at hm
    simp only [TangentSpace, mfderiv_eq_fderiv]
    change (1 - delta) ^ 2 *
        (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
      N.metric.euclideanCoefficients (e x) (fderiv ℝ e x v) (fderiv ℝ e x v)
    simpa only [heta] using hm
  have hreg (p : ℝ) (hp : intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha) :
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[p, H p]) := by
    have hi := m64Intrinsic_normal_map_injective_of_metric_lower N (sub_pos.mpr hdelta1)
      (x := !₂[p, H p]) (by
        simpa only [Matrix.cons_val_zero] using
          hmetric p hp (H p) ⟨hHnonneg p, hHheight p⟩)
    simpa only [TangentSpace, mfderiv_eq_fderiv] using hi
  apply m64Intrinsic_comparison_of_cyclic_retained_strip_ae_outer N e he hH hHnonneg
    hGood hGoodAE hdelta hdeltaSmall hq (by linarith only [hq, hfirst])
    (fun p w hpw hwP hl => hturn p w hpw hwP (hl.trans (by linarith only [hq, hqr])))
    halpha hh (by positivity) (Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_right K 1)))
    (by nlinarith only [hmodel, Real.pi_gt_three]) hrhoSmall hareaLoss
    (fun p _ hp => (hray p hp).mono (Icc_subset_Icc_right (hHheight p)))
    ?_ (fun x _ hxk hxt => hmetric' x hxk hxt) ?_ (fun p _ hp _ => hreg p hp) ?_
  · intro p hp hpk w hw hwk hpw hmeet
    have hf := m64Intrinsic_embedded_normal_collision_cyclic_focusing N
      hK hdelta hdeltaSmall hq hqr hhq hturn halpha harea hbudget hmodel hareaLoss
      e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric
      hpw (by linarith only [hp.1, hw.2])
      ((hHheight p).trans (hcap p)) ((hHheight w).trans (hcap w))
      (hHheight p) (hHheight w)
      ((hray p hpk).mono (Icc_subset_Icc_right (hHheight p)))
      ((hray w hwk).mono (Icc_subset_Icc_right (hHheight w)))
      (hHinside p hp hpk) (hHinside w hw hwk) hmeet
    exact hf.imp And.right And.right
  · intro x _ _ ht
    simpa only [heta] using himage (x 0) (x 1) ⟨ht.1, ht.2.trans (hHheight (x 0))⟩
  · intro p hp hpk ht hg
    have hHeq : H p = height p := by simp only [H, piecewise, hg, ite_true]
    rw [hHeq] at ht ⊢
    rcases (hAnn p).2 with hlast | hi | ho
    · exact (ht.ne hlast).elim
    · exact (hinner p hp hpk hg hi).elim
    · exact ho

end PoincareConjecture
