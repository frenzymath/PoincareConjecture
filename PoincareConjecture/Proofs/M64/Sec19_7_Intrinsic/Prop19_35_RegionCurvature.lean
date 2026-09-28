import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_Continuation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_areaDensity_eq_pullbackVolumeDensity
    (G : RiemannianMetric 2 AnnulusCoordinates) (p : AnnulusCoordinates) :
    Real.sqrt (max 0 (Matrix.det (fun i j : Fin 2 =>
      G.inner p (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j)))) = G.pullbackVolumeDensity id p := by
  have hdensity : G.pullbackVolumeDensity id p =
      Real.sqrt (Matrix.det (fun i j : Fin 2 =>
        G.inner p (EuclideanSpace.basisFun (Fin 2) ℝ i)
          (EuclideanSpace.basisFun (Fin 2) ℝ j))) := by
    unfold RiemannianMetric.pullbackVolumeDensity
    simp only [mfderiv_id, id_eq, ContinuousLinearMap.id_apply]
    rfl
  have hp := (G.contDiffAt_pullbackVolumeDensity (f := id) (x := p) contMDiffAt_id
    (by simpa using Function.injective_id)).2
  have hdet : 0 < Matrix.det (fun i j : Fin 2 =>
      G.inner p (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j)) := by
    exact Real.sqrt_pos.mp (hdensity ▸ hp)
  rw [max_eq_right hdet.le, hdensity]






theorem m64Intrinsic_area_eq_volumeMeasure
    (G : RiemannianMetric 2 AnnulusCoordinates) :
    intrinsicAnnulusArea G = (G.volumeMeasure standardAnnulusDomain).toReal := by
  have hρ (p : AnnulusCoordinates) := G.contDiffAt_pullbackVolumeDensity
    (f := id) (x := p) contMDiffAt_id (by simpa using Function.injective_id)
  have hρc : Continuous (G.pullbackVolumeDensity id) :=
    continuous_iff_continuousAt.mpr (fun p => (hρ p).1.continuousAt)
  have hmeasure : G.volumeMeasure standardAnnulusDomain =
      ∫⁻ p in standardAnnulusDomain, ENNReal.ofReal (G.pullbackVolumeDensity id p) := by
    have h := G.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity
      (OpenPartialHomeomorph.refl AnnulusCoordinates) contMDiffOn_id contMDiffOn_id
      m64Intrinsic_standardAnnulus_isCompact.measurableSet (subset_univ _)
    simpa using h
  rw [intrinsicAnnulusArea]
  simp_rw [m64Intrinsic_areaDensity_eq_pullbackVolumeDensity]
  rw [hmeasure]
  exact integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun p => (hρ p).2.le) hρc.aestronglyMeasurable






theorem m64Intrinsic_region_volume_le_area
    (G : RiemannianMetric 2 AnnulusCoordinates) {S : Set AnnulusCoordinates}
    (hS : S ⊆ standardAnnulusDomain) :
    G.volumeMeasure S < ⊤ ∧ (G.volumeMeasure S).toReal ≤ intrinsicAnnulusArea G := by
  have hfinite := G.volumeMeasure_lt_top_of_isCompact m64Intrinsic_standardAnnulus_isCompact
  refine ⟨(measure_mono hS).trans_lt hfinite, ?_⟩
  rw [m64Intrinsic_area_eq_volumeMeasure]
  exact ENNReal.toReal_mono hfinite.ne (measure_mono hS)







theorem m64Intrinsic_region_gaussian_integral_le_area
    (N : IntrinsicAnnulus) {K : ℝ} (hK : N.GaussianCurvatureBound K)
    {S : Set AnnulusCoordinates} (hS : IsCompact S) (hsub : S ⊆ standardAnnulusDomain) :
    (∫ p in S, N.connection.scalarCurvature p / 2 ∂N.metric.volumeMeasure) ≤
      max K 0 * intrinsicAnnulusArea N.metric := by
  have hcurv : IntegrableOn (fun p => N.connection.scalarCurvature p / 2) S
      N.metric.volumeMeasure :=
    (N.connection.continuous_scalarCurvature.div_const 2).continuousOn.integrableOn_compact hS
  have hconst : IntegrableOn (fun _ : AnnulusCoordinates => max K 0) S
      N.metric.volumeMeasure := continuous_const.continuousOn.integrableOn_compact hS
  have hcomp := setIntegral_mono_on hcurv hconst hS.measurableSet
    (fun p hp => (hK p (hsub hp)).trans (le_max_left _ _))
  have harea := (m64Intrinsic_region_volume_le_area N.metric hsub).2
  calc
    (∫ p in S, N.connection.scalarCurvature p / 2 ∂N.metric.volumeMeasure) ≤
        ∫ _ in S, max K 0 ∂N.metric.volumeMeasure := hcomp
    _ = max K 0 * (N.metric.volumeMeasure S).toReal := by
      rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
      rfl
    _ ≤ max K 0 * intrinsicAnnulusArea N.metric :=
      mul_le_mul_of_nonneg_left harea (le_max_right _ _)

end PoincareConjecture
