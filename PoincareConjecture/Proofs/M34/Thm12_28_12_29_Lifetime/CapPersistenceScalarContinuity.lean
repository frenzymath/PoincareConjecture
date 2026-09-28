import PoincareConjecture.Proofs.M34.Standard.ScalarJetOperator
import PoincareConjecture.Proofs.M34.Mathlib.NeckFiniteBilinearJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

theorem capPersistence_exists_scalar_tolerance {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) {eta : ℝ} (heta : 0 < eta) :
    ∃ zeta : ℝ, 0 < zeta ∧
      ∀ (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (Dh : LeviCivitaData h),
        (∀ j ≤ 2, ∀ a b : Fin n, ‖iteratedFDeriv ℝ j (fun y =>
          h.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
              (EuclideanSpace.basisFun (Fin n) ℝ b) -
            g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
              (EuclideanSpace.basisFun (Fin n) ℝ b)) x‖ ≤ zeta) →
        |Dh.scalarCurvature x - D.scalarCurvature x| < eta := by
  let E := EuclideanSpace ℝ (Fin n)
  let J := spatialJet 2 (fun z : ℝ × E => g.euclideanCoefficients z.2) (0, x)
  have hJ : (twoJetProjection n J).1.IsInvertible := by
    rw [twoJetProjection_spatialJet]
    exact g.inner_isInvertible x
  have hc : ContinuousAt (scalarTwoJet ∘ twoJetProjection n) J :=
    (contDiffAt_scalarTwoJet hJ).continuousAt.comp
      (twoJetProjection n).continuous.continuousAt
  obtain ⟨rho, hrho, hclose⟩ := Metric.continuousAt_iff.mp hc eta heta
  obtain ⟨C, hC, hCb⟩ := exists_piLpBilinearFromCoordinates_jet_bound
    (p := 2) (q := 2) (𝕜 := ℝ) (I := Fin n) (J := Fin n) (E := E) (F := ℝ)
  let zeta := rho / (2 * (C + 1))
  have hzeta : 0 < zeta := div_pos hrho (by positivity)
  have hsmall : C * zeta < rho := by
    have heq : zeta * (2 * (C + 1)) = rho :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨zeta, hzeta, ?_⟩
  intro h Dh hb
  let f : E → Fin n → Fin n → ℝ := fun y a b =>
    h.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) -
      g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)
  have hs (a b : Fin n) : ContDiffAt ℝ ∞ (fun y => f y a b) x :=
    (((h.contDiffAt_euclideanCoefficients x).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).sub
      (((g.contDiffAt_euclideanCoefficients x).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const)
  have heq : (fun y => ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ) (f y)) =
      (fun y => h.euclideanCoefficients y - g.euclideanCoefficients y) := by
    funext y
    simpa only [f, EuclideanSpace.basisFun_apply, sub_apply] using
      ContinuousLinearMap.piLpBilinearFromCoordinates_evaluations
        (h.euclideanCoefficients y - g.euclideanCoefficients y)
  have hjet (j : ℕ) (hj : j ≤ 2) :
      ‖iteratedFDeriv ℝ j h.euclideanCoefficients x -
        iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ C * zeta := by
    have hbound := hCb j f x (fun a b => (hs a b).of_le
      (by exact_mod_cast le_top)) zeta (hb j hj)
    rw [heq] at hbound
    change ‖iteratedFDeriv ℝ j
      (h.euclideanCoefficients - g.euclideanCoefficients) x‖ ≤ _ at hbound
    rwa [iteratedFDeriv_sub_apply
      ((h.contDiffAt_euclideanCoefficients x).of_le (by exact_mod_cast le_top))
      ((g.contDiffAt_euclideanCoefficients x).of_le (by exact_mod_cast le_top))] at hbound
  let Jh := spatialJet 2 (fun z : ℝ × E => h.euclideanCoefficients z.2) (0, x)
  have hdist : dist Jh J < rho := by
    apply lt_of_le_of_lt _ hsmall
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hzeta.le)).mpr
    intro j
    exact hjet j (by omega)
  have hvalue := hclose hdist
  change dist (scalarTwoJet (twoJetProjection n Jh))
    (scalarTwoJet (twoJetProjection n J)) < eta at hvalue
  have hh : scalarTwoJet (twoJetProjection n Jh) = Dh.scalarCurvature x := by
    rw [twoJetProjection_spatialJet]
    exact scalarTwoJet_metricTwoJet Dh x
  have hg : scalarTwoJet (twoJetProjection n J) = D.scalarCurvature x := by
    rw [twoJetProjection_spatialJet]
    exact scalarTwoJet_metricTwoJet D x
  rwa [hh, hg, Real.dist_eq] at hvalue

end PoincareConjecture.M34
