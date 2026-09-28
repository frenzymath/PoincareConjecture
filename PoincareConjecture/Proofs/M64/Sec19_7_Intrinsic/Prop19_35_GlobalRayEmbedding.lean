import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalRayEmbedding
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GlobalCollisionFocusing
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalCurvatureArc

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_good_normal_ray_injOn
    (N : IntrinsicAnnulus) {K delta r q mu alpha h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / q ≤ alpha)
    (hsmall : 4 * (q / 10) * alpha < 1)
    (hfirst : 2 * q < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
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
    (hcap : ∀ p, height p ≤ h)
    (hinterior : ∀ p, ∀ t ∈ Ioo 0 (height p), 1 < ‖e !₂[p, t]‖ ∧ ‖e !₂[p, t]‖ < 2)
    (hgeodesic : ∀ p, N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (height p)))
    (hmetric : ∀ p, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v))
    {a : ℝ} (ha : intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha) :
    InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)) := by
  have halphaPos : 0 < alpha := (div_pos (mul_pos (by norm_num) hdelta) hq).trans_le halpha
  obtain ⟨l, u, hla, hau, hperiod, hgap, hcurv⟩ :=
    m64Intrinsic_exists_local_curvature_arc N
      (ha.trans_lt (by linarith only [halphaPos] : alpha < 2 * alpha))
      (sub_pos.mpr hfirst)
  have hkappa : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_right K 1))
  have hangle : Real.sqrt (max K 1) * (q / 10) ≤ Real.pi / 4 := by
    nlinarith only [hmodel, Real.pi_gt_three]
  have hcritical : 2 * (q / 10) * (2 * alpha) < 1 := by nlinarith only [hsmall]
  have hbefore (p A : ℝ) (hA : A < h)
      (hinside : ∀ t ∈ Ioc 0 A, 1 < ‖e !₂[p, t]‖ ∧ ‖e !₂[p, t]‖ < 2) :
      A ≤ height p := by
    by_contra hn
    have hlt : height p < A := lt_of_not_ge hn
    have hi := hinside (height p) ⟨(hAnn p).1, hlt.le⟩
    rcases (hAnn p).2 with heq | heq | heq
    · linarith only [heq, hlt, hA]
    · rw [heq] at hi
      exact (lt_irrefl (1 : ℝ)) hi.1
    · rw [heq] at hi
      exact (lt_irrefl (2 : ℝ)) hi.2
  have hordered (p w : ℝ) (hp : p ∈ Ioo l u) (hw : w ∈ Ioo l u) (hpw : p < w)
      (A B : ℝ) (hA : A ∈ Ioo 0 h) (hB : B ∈ Ioo 0 h)
      (hiA : InjOn (fun t => e !₂[p, t]) (Icc 0 A))
      (hiB : InjOn (fun t => e !₂[w, t]) (Icc 0 B))
      (hinsideA : ∀ t ∈ Ioc 0 A, 1 < ‖e !₂[p, t]‖ ∧ ‖e !₂[p, t]‖ < 2)
      (hinsideB : ∀ t ∈ Ioc 0 B, 1 < ‖e !₂[w, t]‖ ∧ ‖e !₂[w, t]‖ < 2) :
      e !₂[p, A] ≠ e !₂[w, B] := by
    intro hmeet
    have hfocus := m64Intrinsic_embedded_normal_collision_cyclic_focusing N
      hK hdelta hdeltaSmall hq hqr hhq hturn halpha harea hbudget hmodel hareaLoss
      e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric
      hpw (by linarith only [hperiod, hp.1, hw.2]) hA.2.le hB.2.le
      (hbefore p A hA.2 hinsideA) (hbefore w B hB.2 hinsideB) hiA hiB
      (fun t ht => ⟨(hinsideA t ht).1, (hinsideA t ht).2.le⟩)
      (fun t ht => ⟨(hinsideB t ht).1, (hinsideB t ht).2.le⟩)
      ⟨A, ⟨hA.1.le, le_rfl⟩, B, ⟨hB.1.le, le_rfl⟩, hmeet⟩
    have hlength := (m64Intrinsic_boundaryLength_subarc_quantitative N one_ne_zero
      hp.1.le hpw.le hw.2.le).1
    have hleft := m64Intrinsic_boundaryLength_nonneg N 1 l p hp.1.le
    exact m64Intrinsic_no_local_cyclic_focusing N hpw (by positivity) hkappa hangle hcritical
      (fun x hx => hcurv x ⟨hp.1.le.trans hx.1, hx.2.trans hw.2.le⟩)
      (by linarith only [hlength, hleft, hgap]) hfocus
  have hreg : ∀ t ∈ Icc 0 (height a),
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]) := by
    intro t ht
    have hc : 0 < 1 - delta := by linarith only [hdeltaSmall]
    have hi := m64Intrinsic_normal_map_injective_of_metric_lower N hc
      (x := !₂[a, t]) (by
        simpa only [Matrix.cons_val_zero] using hmetric a ha t ht)
    simpa only [TangentSpace, mfderiv_eq_fderiv] using hi
  apply m64Intrinsic_normal_ray_injOn_of_local_prefix_separation he hbase (hAnn a).1 (hcap a)
    (by rw [(hderiv a).deriv]; exact hinward0 a) (hinterior a) hreg isOpen_Ioo ⟨hla, hau⟩
  intro p hp w hw hpw A hA B hB hiA hiB hinsideA hinsideB
  rcases lt_or_gt_of_ne hpw with hpw | hwp
  · exact hordered p w hp hw hpw A B hA hB hiA hiB hinsideA hinsideB
  · exact (hordered w p hw hp hwp B A hB hA hiB hiA hinsideB hinsideA).symm

end PoincareConjecture
