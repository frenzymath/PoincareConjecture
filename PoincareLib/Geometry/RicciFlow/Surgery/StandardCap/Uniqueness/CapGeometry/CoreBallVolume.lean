import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.CurvatureRadius
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.ScalarLowerBound.ScalarFloor
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.ScalarOperators.CompactScalarConvergence
import PoincareLib.Geometry.Riemannian.Curvature.ThreeDimensional

/-!
# Noncollapse at the actual scalar-curvature radius

Morgan-Tian Definition 9.72 and Remark 9.73, pp. 230-231, in
Theorem 12.28, pp. 323-324. Finite Harnack controls the preceding
half-radius cylinder. The selected standard flow's own noncollapsing
certificate then gives a uniform cubic volume lower bound.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.LeviCivitaData

/-- Remark 9.73 in Theorem 12.28: in dimension three, nonnegative
sectional curvature bounds the actual full curvature norm by the scalar. -/
theorem curvatureTensorNorm_le_scalar_of_nonnegative_sectional_three
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (hsec : ∀ v w : TangentSpace (𝓡 3) x,
      0 ≤ D.curvatureTensor x v w v w) : D.curvatureTensorNorm x ≤ D.scalarCurvature x := by
  obtain ⟨a, b, c, hab, hbc, hleast, hscalar, hnorm⟩ :=
    D.three_dimensional_curvature_spectrum hD x
  have hc : 0 ≤ c := by
    rw [← hleast]
    apply Real.sInf_nonneg
    rintro k ⟨v, w, _, rfl⟩
    exact hsec v w
  have hb : 0 ≤ b := hc.trans hbc
  have ha : 0 ≤ a := hb.trans hab
  have hnormpos : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  rw [hscalar]
  nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

end PoincareMT.LeviCivitaData

namespace PoincareMT.RepairedStandardCapExistenceData

/-- Definition 9.72 in Theorem 12.28: an actual scalar-curvature
ball with r^2 <= t and r below the supplied noncollapsing scale has
volume at least kappa r^3 / 8. The full cap can therefore retain a
strict reciprocal volume constant larger than 8/kappa. -/
theorem scalar_curvature_ball_volume_lower (P : RicciFlowCurvatureTheory.{0})
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (N : StandardFlowNoncollapsingCertificate E.flow) {t r : ℝ}
    (ht : t ∈ Ico 0 E.flow.base.lifetime) (hr : 0 < r) (hradius : r ≤ N.radius)
    (hrt : r ^ 2 ≤ t) (y : StandardCapSpace)
    (hscale : scalarCurvatureSupOn (E.flow.metric t) (E.flow.connection t)
      ((E.flow.metric t).ball y r) = r⁻¹ ^ 2) :
    ENNReal.ofReal (N.kappa / 8 * r ^ 3) ≤
      calibratedMetricVolume (E.flow.metric t) ((E.flow.metric t).ball y r) := by
  have htpos : 0 < t := (sq_pos_of_pos hr).trans_le hrt
  have hRcont : Continuous (E.flow.connection t).scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P (E.flow.connection t)).continuous
  have hcompact := Proofs.M09.isCompact_closure_metric_ball (E.flow.metric t)
    (E.complete t ht) y r
  have hbounded : BddAbove (range fun z : (E.flow.metric t).ball y r =>
      (E.flow.connection t).scalarCurvature z.1) := by
    rw [← image_eq_range]
    exact (hcompact.bddAbove_image hRcont.continuousOn).mono (image_mono subset_closure)
  have hterminal (z : StandardCapSpace) (hz : z ∈ (E.flow.metric t).ball y (r / 2)) :
      (E.flow.connection t).scalarCurvature z ≤ r⁻¹ ^ 2 := by
    rw [← hscale]
    exact le_csSup hbounded ⟨⟨z, hz.trans_le (ENNReal.ofReal_le_ofReal (by linarith))⟩, rfl⟩
  have hhalf : 0 < r / 2 := half_pos hr
  have hhalfradius : r / 2 ≤ N.radius := (by linarith : r / 2 ≤ r).trans hradius
  have hhalft : (r / 2) ^ 2 ≤ t := by nlinarith
  have hparabolic : ∀ s ∈ Ioc (t - (r / 2) ^ 2) t,
      ∀ z ∈ (E.flow.metric t).ball y (r / 2),
        |(E.flow.connection s).curvatureTensorNorm z| ≤ (r / 2)⁻¹ ^ 2 := by
    intro s hs z hz
    have hspos : 0 < s := by nlinarith [sq_nonneg r, hs.1]
    have hsmem : s ∈ Ico 0 E.flow.base.lifetime := ⟨hspos.le, hs.2.trans_lt ht.2⟩
    have hscalar : (E.flow.connection s).scalarCurvature z ≤ 2 * r⁻¹ ^ 2 := by
      rcases hs.2.eq_or_lt with rfl | hst
      · exact (hterminal z hz).trans (by nlinarith [sq_nonneg r⁻¹])
      · have hH := E.time_mul_scalar_le P hspos hst (E.lifetime_one ▸ ht.2) z
        have hnonneg := (E.scalar_pos hsmem z).le
        have htime : t / 2 ≤ s := by nlinarith [sq_nonneg r, hs.1]
        have hfirst := mul_le_mul_of_nonneg_left htime hnonneg
        have hlast := mul_le_mul_of_nonneg_right (hterminal z hz) htpos.le
        nlinarith
    have hnorm := (E.flow.connection s).curvatureTensorNorm_le_scalar_of_nonnegative_sectional_three
      (P.tensor_calculus 3 StandardCapSpace _ _) z (E.nonnegative_sectional s hsmem z)
    rw [abs_of_nonneg (show 0 ≤ (E.flow.connection s).curvatureTensorNorm z from
      Real.sqrt_nonneg _)]
    refine (hnorm.trans hscalar).trans ?_
    rw [inv_div, div_eq_mul_inv, mul_pow]
    norm_num
    nlinarith [inv_nonneg.mpr (sq_nonneg r)]
  have hvol := N.bound t ht y (r / 2) hhalf hhalfradius hhalft hparabolic
  have hball : (E.flow.metric t).ball y (r / 2) ⊆ (E.flow.metric t).ball y r :=
    fun z hz => hz.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hcoefficient : N.kappa * (r / 2) ^ 3 = N.kappa / 8 * r ^ 3 := by ring
  rw [hcoefficient] at hvol
  exact hvol.trans (measure_mono hball)

end PoincareMT.RepairedStandardCapExistenceData
