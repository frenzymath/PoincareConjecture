import PoincareConjecture.Proofs.M34.Standard.ScalarJetConvergence
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

noncomputable def scalarLaplacianJet (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 4) : ℝ :=
  let K := twoJetProjection n (baseProjection 2 2 J)
  ∑ i : Fin n, (
    scalarJetOperator n 2 J ![EuclideanSpace.basisFun (Fin n) ℝ i,
      K.1.inverse (EuclideanSpace.proj i)] -
    scalarJetOperator n 1 (truncate 3 J) ![jetChristoffel K
      (EuclideanSpace.basisFun (Fin n) ℝ i) (K.1.inverse (EuclideanSpace.proj i))])

theorem continuousOn_scalarLaplacianJet (n : ℕ) :
    ContinuousOn (scalarLaplacianJet n) (curvatureJetDomain n 2) := by
  intro J hJ
  apply ContinuousAt.continuousWithinAt
  have hK : ContDiff ℝ ∞ (fun A => twoJetProjection n (baseProjection 2 2 A)) :=
    ((twoJetProjection n).comp (baseProjection 2 2)).contDiff
  have hinv : ((twoJetProjection n (baseProjection 2 2 J)).1).IsInvertible := hJ
  have hI : ContDiffAt ℝ ∞
      (fun A : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 4 =>
        (twoJetProjection n (baseProjection 2 2 A)).1.inverse) J := by
    convert! hinv.contDiffAt_map_inverse.comp J hK.contDiffAt.fst using 1
  have h2 := ((contDiffOn_scalarJetOperator n 2).contDiffAt
    ((isOpen_curvatureJetDomain n 2).mem_nhds hJ)).continuousAt
  have h1 := (((contDiffOn_scalarJetOperator n 1).contDiffAt
    ((isOpen_curvatureJetDomain n 1).mem_nhds hJ)).comp J
      (truncate (E := EuclideanSpace ℝ (Fin n))
        (V := MetricCoefficient n) 3).contDiff.contDiffAt).continuousAt
  unfold scalarLaplacianJet
  apply tendsto_finsetSum
  intro i _
  have hi := hI.clm_apply (contDiffAt_const (c := EuclideanSpace.proj (𝕜 := ℝ) i))
  have hΓ := (contDiffAt_jetChristoffel hinv
    (u := fun _ => EuclideanSpace.basisFun (Fin n) ℝ i)
    (v := fun A => A.1.inverse (EuclideanSpace.proj i))
    contDiffAt_const (hinv.contDiffAt_map_inverse.comp _ contDiffAt_fst |>.clm_apply
      contDiffAt_const)).comp J hK.contDiffAt
  apply (h2.eval ?_).sub (h1.eval ?_)
  · apply continuousAt_pi.mpr
    intro j
    fin_cases j
    · exact continuousAt_const
    · exact hi.continuousAt
  · exact continuousAt_pi.mpr (fun j => by fin_cases j; exact hΓ.continuousAt)

theorem scalarLaplacianJet_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    scalarLaplacianJet n (spatialJet 4
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x)) =
      D.laplacian D.scalarCurvature x := by
  have hR : ContDiffAt ℝ ∞ D.scalarCurvature x :=
    contMDiffAt_iff_contDiffAt.mp (contMDiff_scalarCurvature D x)
  have hK := congrArg (twoJetProjection n) (baseProjection_spatialJet 2 2
    (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x))
  rw [twoJetProjection_spatialJet] at hK
  rw [D.laplacian_eq_sum_hessian_inverse hR]
  simp only [scalarLaplacianJet, scalarJetOperator_spatialJet D,
    truncate_spatialJet, hK]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.hessian_eq_fderiv_sub_christoffel hR, iteratedFDeriv_two_apply,
    iteratedFDeriv_one_apply]
  rfl

end PoincareConjecture.M34
