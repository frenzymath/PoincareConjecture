import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false

set_option maxSynthPendingDepth 12

open scoped ContDiff Topology

namespace PoincareConjecture.M36

open PoincareConjecture.SpacetimeBounds

theorem exists_jetCurvature_component_bounds (J0 : MetricTwoJet 3)
    (hJ0 : J0.1.IsInvertible) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, 0 < K ∧
      ∀ J : MetricTwoJet 3, ‖J - J0‖ < r →
        (∀ i j k l : Fin 3,
          |jetCurvature J (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)
              (EuclideanSpace.basisFun (Fin 3) ℝ k)
              (EuclideanSpace.basisFun (Fin 3) ℝ l) -
            jetCurvature J0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)
              (EuclideanSpace.basisFun (Fin 3) ℝ k)
              (EuclideanSpace.basisFun (Fin 3) ℝ l)| ≤ K * ‖J - J0‖) ∧
        (∀ i j : Fin 3,
          ‖jetChristoffel J (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j) -
            jetChristoffel J0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)‖ ≤ K * ‖J - J0‖) := by
  classical
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let Phi : MetricTwoJet 3 →
      ((Fin 4 → Fin 3) → ℝ) × ((Fin 2 → Fin 3) → EuclideanSpace ℝ (Fin 3)) :=
    fun J => (fun a => jetCurvature J (e (a 0)) (e (a 1)) (e (a 2)) (e (a 3)),
      fun a => jetChristoffel J (e (a 0)) (e (a 1)))
  have hPhi : ContDiffAt ℝ ∞ Phi J0 :=
    (contDiffAt_pi.mpr fun a => contDiffAt_jetCurvature hJ0 _ _ _ _).prodMk
      (contDiffAt_pi.mpr fun a =>
        contDiffAt_jetChristoffel hJ0 contDiffAt_const contDiffAt_const)
  obtain ⟨L, U, hU, hLip⟩ :=
    (hPhi.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, hr, max (L : ℝ) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro J hJ
  have hnorm : ‖Phi J - Phi J0‖ ≤ (L : ℝ) * ‖J - J0‖ := by
    simpa only [dist_eq_norm] using hLip.dist_le_mul J
      (hball (show J ∈ Metric.ball J0 r by simpa only [Metric.mem_ball, dist_eq_norm] using hJ))
      J0 (hball (Metric.mem_ball_self hr))
  have hbound : ‖Phi J - Phi J0‖ ≤ max (L : ℝ) 1 * ‖J - J0‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  constructor
  · intro i j k l
    have h := (norm_le_pi_norm (Phi J - Phi J0).1 ![i, j, k, l]).trans
      ((norm_fst_le (Phi J - Phi J0)).trans hbound)
    simpa [Phi, e] using h
  · intro i j
    have h := (norm_le_pi_norm (Phi J - Phi J0).2 ![i, j]).trans
      ((norm_snd_le (Phi J - Phi J0)).trans hbound)
    simpa [Phi, e] using h

end PoincareConjecture.M36
