import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.GaussBonnet.Scalar
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.GaussBonnet.Contraction
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.FillingArea.Inputs

/-!
# Gauss--Bonnet for the supplied actual minimal disk

The actual logarithmic curvature inequality, genuine Ricci-density
integrability and pointwise manifold Gauss comparison prove the
unchanged geometric input used by the filling-area inequality.
Source: MT Lemma 19.2 and Claim 19.5, pp. 438--441;
M65 derivation 45, Actual Ricci Contraction at the Final Disk.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareMT

universe u

/-- The literal supplied-disk Gauss--Bonnet input is proved from the
frozen record and genuine smooth regular Jordan boundary. All branch,
curvature, Stokes and flux premises are discharged by the actual
record consumers. Source: MT 19.2 and Claim 19.5, pp. 438--441;
derivation 45, final actual contraction. -/
theorem m65SuppliedDiskGaussBonnet {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) :
    M65SuppliedDiskGaussBonnet g D := by
  intro gamma S hsmooth hregular hinj W hW
  obtain ⟨hG, hB, hGB⟩ := S.logarithmicGaussDensity_gaussBonnet hinj hsmooth hregular W hW
  have hQ := S.gaussContraction_integrable
  have hnull : ∀ᵐ z : LoopPlane ∂volume, z ∉ sphere (0 : LoopPlane) 1 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using
      Measure.addHaar_sphere volume (0 : LoopPlane) 1
  have hpoint : ∀ᵐ z ∂volume.restrict loopDiskSet,
      M65Gauss.logarithmicGaussDensity S.conformalFactor z ≤
        m65PlaneRicciTraceDensity D S.disk.map z -
          D.scalarCurvature (S.disk.map z) * m60AreaDensity g S.disk.map z / 2 := by
    filter_upwards [ae_restrict_mem (measurableSet_closedBall : MeasurableSet loopDiskSet),
      ae_restrict_of_ae hnull,
      ae_restrict_of_ae (S.conformalFactor_finite_zeros.countable.ae_notMem volume)]
        with z hz hboundary hbranch
    have hzU : z ∈ ball (0 : LoopPlane) 1 :=
      mem_ball_zero_iff.mpr (lt_of_le_of_ne (mem_closedBall_zero_iff.mp hz)
        (by simpa only [mem_sphere_zero_iff_norm] using hboundary))
    have hpos : 0 < S.conformalFactor z :=
      lt_of_le_of_ne (S.conformalFactor_nonneg z) (fun h => hbranch ⟨hz, h.symm⟩)
    exact S.logarithmicGaussDensity_le_gaussContraction hzU hpos
  have hIntegral := integral_mono_ae hG hQ hpoint
  refine ⟨hQ, hB, ?_⟩
  exact hGB.trans (sub_le_sub_right hIntegral _)

end PoincareMT
