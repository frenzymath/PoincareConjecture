import PoincareConjecture.Proofs.M64.Mathlib.ObservedCoordinateMetric
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.C2BoundaryTargetCoordinates










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture




theorem m64BoundaryCoordinate_metric_data {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (A : EuclideanSpace ℝ (Fin n) → M)
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    {rho K : ℝ} (hrho : 0 < rho) (hK : 0 < K)
    (hA : ContMDiffOn (𝓡 n) (𝓡 n) 1 A (ball 0 (2 * rho)))
    (hH : ContDiff ℝ 1 H)
    (hinv : ∀ y ∈ ball 0 (2 * rho), H (e (A y)) = y)
    (hDH : ∀ y, ‖fderiv ℝ H y‖ ≤ K)
    (hDA : ∀ y ∈ closedBall 0 rho, ‖fderiv ℝ (e ∘ A) y‖ ≤ K)
    (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hB : Continuous B) {bound : ℝ} (hbound : ∀ q, ‖B q‖ ≤ bound)
    (hsymm : ∀ q v w, B q v w = B q w v) (hpos : ∀ q v, 0 ≤ B q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : EuclideanSpace ℝ (Fin m)),
      v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ C * B q v v) :
    let G := m64ObservedCoordinateMetric (e ∘ A) (B ∘ A)
    ∃ lower upper : ℝ, 0 < lower ∧ 0 ≤ upper ∧
      ContinuousOn G (closedBall 0 rho) ∧
      ∀ y ∈ closedBall 0 rho,
        (∀ v w, G y v w = G y w v) ∧
        (∀ v, lower * ‖v‖ ^ 2 ≤ G y v v) ∧ ∀ v, G y v v ≤ upper * ‖v‖ ^ 2 := by
  let E := EuclideanSpace ℝ (Fin n)
  have hsub : closedBall (0 : E) rho ⊆ ball 0 (2 * rho) :=
    closedBall_subset_ball (by linarith)
  have hJ : ContDiffOn ℝ 1 (e ∘ A) (ball (0 : E) (2 * rho)) := by
    intro y hy
    exact (contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp y
      (hA.contMDiffAt (isOpen_ball.mem_nhds hy)))).contDiffWithinAt
  have hQ : ContinuousOn (B ∘ A) (closedBall (0 : E) rho) :=
    hB.comp_continuousOn (hA.continuousOn.mono hsub)
  have hmetricCoercive (y : E) (hy : y ∈ closedBall 0 rho) (v : E) :
      ‖fderiv ℝ (e ∘ A) y v‖ ^ 2 ≤
        C * B (A y) (fderiv ℝ (e ∘ A) y v) (fderiv ℝ (e ∘ A) y v) := by
    apply hcoercive
    have hd := congrArg (fun L : E →L[ℝ] EuclideanSpace ℝ (Fin m) => L v)
      (mfderiv_comp y (he.mdifferentiable (by simp) _)
        ((hA.contMDiffAt (isOpen_ball.mem_nhds (hsub hy))).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at hd
    exact ⟨mfderiv (𝓡 n) (𝓡 n) A y v, hd.symm⟩
  obtain ⟨hlower, hupper, hmetric⟩ := m64ObservedCoordinateMetric_bounds
    isOpen_ball hJ hH hsub (show EqOn (H ∘ (e ∘ A)) id (ball 0 (2 * rho)) from hinv)
    hC hK hK.le (le_max_right bound 0)
    (fun y _ => hDH (e (A y))) hDA
    (fun y _ => (hbound (A y)).trans (le_max_left bound 0))
    (fun y _ => hsymm (A y)) (fun y _ => hpos (A y)) hmetricCoercive
  exact ⟨1 / (K ^ 2 * (C + 1)), max bound 0 * K ^ 2, hlower, hupper,
    m64ObservedCoordinateMetric_continuousOn isOpen_ball hJ hsub hQ, hmetric⟩

end PoincareConjecture
