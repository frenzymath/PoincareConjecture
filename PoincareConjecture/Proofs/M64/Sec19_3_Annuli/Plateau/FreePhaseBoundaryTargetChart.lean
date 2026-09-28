import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTargetCoordinates
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseTargetAngle














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}




theorem auxiliaryCircle_bounded_boundary_phase_chart
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e)
    (hemb : Topology.IsEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    (Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hR : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    (C : ℝ → Q.charts.Point)
    (hC : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 ((n + 1) + 1)) 1 C)
    (hregular : curveVelocity (n := (n + 1) + 1) C 0 ≠ 0) :
    ∃ (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin ((n + 1) + 1)))
      (A : EuclideanSpace ℝ (Fin ((n + 1) + 1)) → Q.charts.Point)
      (beta : EuclideanSpace ℝ (Fin ((n + 1) + 1)) → ℝ)
      (L : NNReal) (rho delta eta K : ℝ),
      0 < rho ∧ 0 < delta ∧ 0 < eta ∧ eta ≤ rho / 4 ∧ 0 < K ∧
      H (e (C 0)) = 0 ∧ A 0 = C 0 ∧
      ContDiff ℝ 1 H ∧ LipschitzWith L H ∧ (∀ y, ‖fderiv ℝ H y‖ ≤ K) ∧
      ContMDiffOn (𝓡 ((n + 1) + 1)) (𝓡 ((n + 1) + 1)) 1 A (ball 0 (2 * rho)) ∧
      ContDiffOn ℝ 1 beta (ball 0 (2 * rho)) ∧
      (∀ y ∈ ball 0 (2 * rho), Robs (e (A y)) =
        Proofs.M58.angularPoint ((curvePeriod / circumference) * beta y)) ∧
      (∀ y ∈ closedBall 0 rho, ‖fderiv ℝ (e ∘ A) y‖ ≤ K) ∧
      (∀ q : Q.charts.Point, dist (e q) (e (C 0)) < delta →
        ‖H (e q)‖ < rho / 4 ∧ A (H (e q)) = q) ∧
      ∀ t ∈ Ioo (-eta) eta,
        H (e (C t)) = EuclideanSpace.single 0 t ∧
        A (EuclideanSpace.single 0 t) = C t := by
  let := Q.charts.chartedSpace
  obtain ⟨U, angle, hU, hCU, hangle, hquot⟩ :=
    auxiliaryCircle_originalPhase_local P Q (C 0)
  obtain ⟨H, A, L, rho, delta, eta, K, hrho, hdelta, heta, hetarho, hK,
    hH0, hA0, hH, hLip, hHD, hA, hAU, hAD, hcap, haxis⟩ :=
    m64ChartReadable_bounded_boundary_chart e he hemb hread C hC hregular hU hCU
  refine ⟨H, A, angle ∘ A, L, rho, delta, eta, K, hrho, hdelta, heta, hetarho, hK,
    hH0, hA0, hH, hLip, hHD, hA, ?_, ?_, hAD, hcap, haxis⟩
  · exact contMDiffOn_iff_contDiffOn.mp ((hangle.of_le (by simp)).comp hA hAU)
  · intro y hy
    rw [hR, ← hquot (A y) (hAU hy), planarCircleObservation_quotient]
    rfl

end PoincareConjecture.M64
