import PoincareConjecture.Proofs.M34.Standard.ScalarJetOperator
import PoincareConjecture.Proofs.M34.Standard.ScalarGradientNorm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap



noncomputable def scalarDifferentialNormJet (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 3) : ℝ :=
  let L := continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ
    (scalarJetOperator n 1 J)
  Real.sqrt (L ((twoJetProjection n (baseProjection 2 1 J)).1.inverse L))



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

end PoincareConjecture.M34
