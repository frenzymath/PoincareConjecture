import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AnnularNormalReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ForwardBoundaryParameter
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalNormalCalculus





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_no_transverse_inner_endpoint
    (N : IntrinsicAnnulus) {K delta r q mu alpha h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hh : 0 < h) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / q ≤ alpha)
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
    (hgeodesic : ∀ p, N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (height p)))
    (hmetric : ∀ p, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v))
    {a : ℝ} (ha : a ∈ Ico (0 : ℝ) rampPeriod)
    (hgood : intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha)
    (hcap : height a ≤ h)
    (hinside : ∀ t ∈ Ioo 0 (height a), 1 < ‖e !₂[a, t]‖ ∧ ‖e !₂[a, t]‖ < 2)
    (hinj : InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)))
    (htransverse : ∀ t b : ℝ, e !₂[a, t] = intrinsicAnnulusBoundary 1 b →
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]) →
      LinearIndependent ℝ
        (![deriv (intrinsicAnnulusBoundary 1) b, fderiv ℝ e !₂[a, t] !₂[0, 1]] :
          Fin 2 → AnnulusCoordinates)) : ‖e !₂[a, height a]‖ ≠ 1 := by
  intro hinner
  have hneq : e !₂[a, height a] ≠ intrinsicAnnulusBoundary 1 a := by
    intro heq
    have ht := hinj ⟨(hAnn a).1.le, le_rfl⟩ ⟨le_rfl, (hAnn a).1.le⟩
      (heq.trans (hbase a).symm)
    exact (ne_of_gt (hAnn a).1) ht
  obtain ⟨b, hab, hperiod, hb⟩ := m64Intrinsic_exists_forward_boundary_parameter ha hinner hneq
  have hreg : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, height a]) := by
    have hc : 0 < 1 - delta := by linarith only [hdeltaSmall]
    have hi := m64Intrinsic_normal_map_injective_of_metric_lower N hc
      (x := !₂[a, height a]) (by
        simpa only [Matrix.cons_val_zero] using
          hmetric a hgood (height a) ⟨(hAnn a).1.le, le_rfl⟩)
    simpa only [TangentSpace, mfderiv_eq_fderiv] using hi
  have hterminal : LinearIndependent ℝ
      (![deriv (intrinsicAnnulusBoundary 1) b,
        deriv (fun t => e !₂[a, t]) (height a)] : Fin 2 → AnnulusCoordinates) := by
    rw [m64Intrinsic_coordinate_normal_ray_deriv
      (he.differentiable (by simp) !₂[a, height a])]
    exact htransverse (height a) b hb hreg
  have hsmooth : ContDiff ℝ ∞ (fun t => e !₂[a, t]) := he.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id)
  exact m64Intrinsic_no_annular_normal_return N hK hdelta hdeltaSmall hq hqr hh hhq
    hturn halpha harea hbudget hmodel hareaLoss hsmooth hab hperiod (hAnn a).1 hcap
    hinj (hbase a) hb hinside (hgeodesic a)
    (by rw [(hderiv a).deriv, hbase a]; exact hunit0 a)
    (by rw [(hderiv a).deriv]; exact horth0 a)
    (by rw [(hderiv a).deriv]; exact hinward0 a) hterminal
    e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric

end PoincareConjecture
