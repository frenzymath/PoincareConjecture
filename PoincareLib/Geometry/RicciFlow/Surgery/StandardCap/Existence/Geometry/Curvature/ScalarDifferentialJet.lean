import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.ScalarJetOperator
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.ScalarGradientNorm

/-!
# The metric norm of the scalar differential from three metric jets

Metric duality computes the squared norm as dR(g inverse dR), with no
choice of varying orthonormal frames. Source: Morgan-Tian Theorem 12.28,
pp. 323-324; included-cylinder-geometric-readouts.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Scalar differential operators have dependent metric-jet input spaces.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

/-- The metric norm of the formal scalar differential, computed from
the metric three-jet (Theorem 12.28, pp. 323-324). -/
noncomputable def scalarDifferentialNormJet (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 3) : ℝ :=
  let L := continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ
    (scalarJetOperator n 1 J)
  Real.sqrt (L ((twoJetProjection n (baseProjection 2 1 J)).1.inverse L))

/-- The formal scalar differential norm is continuous at every
invertible metric three-jet, including zero differential (Theorem 12.28). -/
theorem continuousOn_scalarDifferentialNormJet (n : ℕ) :
    ContinuousOn (scalarDifferentialNormJet n) (curvatureJetDomain n 1) := by
  intro J hJ
  apply ContinuousAt.continuousWithinAt
  have hS := ((contDiffOn_scalarJetOperator n 1).contDiffAt
    ((isOpen_curvatureJetDomain n 1).mem_nhds hJ)).continuousAt
  have hL := (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).continuous
    |>.continuousAt.comp hS
  have hB : ContDiff ℝ ∞ (fun A => (twoJetProjection n (baseProjection 2 1 A)).1) :=
    ((twoJetProjection n).comp (baseProjection 2 1)).contDiff.fst
  have hinv : ((twoJetProjection n (baseProjection 2 1 J)).1).IsInvertible := hJ
  have hI : ContinuousAt
      (fun A : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 3 =>
        (twoJetProjection n (baseProjection 2 1 A)).1.inverse) J := by
    convert! (hinv.contDiffAt_map_inverse.comp J hB.contDiffAt).continuousAt using 1
  exact (hL.clm_apply (hI.clm_apply hL)).sqrt

/-- On an actual Euclidean metric the formal differential norm is
the selected-metric norm of its genuine scalar gradient (Theorem 12.28). -/
theorem scalarDifferentialNormJet_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    scalarDifferentialNormJet n (spatialJet 3
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x)) =
      g.tangentNorm x (D.gradient D.scalarCurvature x) := by
  have hK := congrArg (twoJetProjection n) (baseProjection_spatialJet 2 1
    (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x))
  rw [twoJetProjection_spatialJet] at hK
  have hL : continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ
      (iteratedFDeriv ℝ 1 D.scalarCurvature x) = fderiv ℝ D.scalarCurvature x := by
    ext v
    simp only [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rfl
  simp only [scalarDifferentialNormJet, scalarJetOperator_spatialJet D, hK, hL]
  unfold RiemannianMetric.tangentNorm
  rw [D.inner_gradient]
  simp +instances only [LeviCivitaData.gradient, mvfderiv, mfderiv_eq_fderiv,
    NormedSpace.fromTangentSpace]
  rfl

end PoincareMT.M34
