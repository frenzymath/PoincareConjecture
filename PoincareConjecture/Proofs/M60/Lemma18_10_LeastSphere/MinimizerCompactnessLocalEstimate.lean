import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessBounds
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

local instance suCompactLocalBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactLocalBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suCompactLocalTrilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactLocalTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suCompactLocalChristoffelNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactLocalChristoffelNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace


def suNormalizedAlphaCoordinateSource (g : RiemannianMetric n M) (p : M)
    (u : LoopPlane → E) (lambda : LoopPlane → ℝ) (rho c : ℝ) (x : LoopPlane) : E :=
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  let V := fun i : Fin 2 => fderiv ℝ u x (b i)
  let d := rho ^ 2 * lambda x + ∑ i : Fin 2, G (u x) (V i) (V i)
  suAlphaLowerTerm (christoffelBilinear G (u x)) (G (u x)) (fderiv ℝ G (u x))
    V (lambda x) (fun i => fderiv ℝ lambda x (b i)) d c

set_option maxHeartbeats 1600000 in





theorem suAlphaChart_uniform_nearLaplacian
    (g : RiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 n) p).target)
    (u : ℕ → LoopPlane → E) (lambda : ℕ → LoopPlane → ℝ) (rho c : ℕ → ℝ)
    (center : LoopPlane) {R D L N : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (Metric.ball center R))
    (hlambda : ∀ j, ContDiffOn ℝ ∞ (lambda j) (Metric.ball center R))
    (hrange : ∀ j, MapsTo (u j) (Metric.ball center R) K)
    (hgrad : ∀ j x, x ∈ Metric.ball center R → ∀ i : Fin 2,
      ‖fderiv ℝ (u j) x (b i)‖ ≤ D)
    (hl : ∀ j x, x ∈ Metric.ball center R → 0 < lambda j x ∧ (lambda j x)⁻¹ ≤ L)
    (hdl : ∀ j x, x ∈ Metric.ball center R → ∀ i : Fin 2,
      ‖fderiv ℝ (lambda j) x (b i)‖ ≤ N)
    (hrho : ∀ j, 0 < rho j) (hc : Tendsto c atTop (𝓝 0))
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (heq : ∀ j x, x ∈ Metric.ball center R →
      let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      let Gamma := christoffelBilinear G
      let w := fun y => ((rho j) ^ 2 + (∑ i : Fin 2,
        G (u j y) (fderiv ℝ (u j) y (b i)) (fderiv ℝ (u j) y (b i))) /
          lambda j y) ^ (c j)
      ∑ i : Fin 2, covDerivAlong Gamma (u j)
        (fun y => w y • fderiv ℝ (u j) y (b i)) (b i) x = 0) :
    ∃ A F : ℝ, 0 ≤ A ∧ 0 ≤ F ∧
      (∀ j x, x ∈ Metric.ball center R → ‖u j x‖ ≤ A ∧
        ∀ i : Fin 2, ‖fderiv ℝ (u j) x (b i)‖ ≤ A) ∧
      (∀ j x, x ∈ Metric.ball center R →
        ‖suNormalizedAlphaCoordinateSource g p (u j) (lambda j) (rho j) (c j) x‖ ≤ F) ∧
      ∀ delta : ℝ, 0 < delta → ∀ᶠ j in atTop, ∀ x ∈ Metric.ball center R,
        ‖(∑ i : Fin 2, suCoordinateHessian (u j) x i i) -
          suNormalizedAlphaCoordinateSource g p (u j) (lambda j) (rho j) (c j) x‖ ≤
          delta * Real.sqrt (∑ i : Fin 2, ∑ k : Fin 2,
            ‖suCoordinateHessian (u j) x i k‖ ^ 2) := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  let Gamma := christoffelBilinear G
  obtain ⟨kappa, B, hkappa, hB, -, hGB, hcoer⟩ := suAlpha_coordinate_metric_bounds g p hK hKt
  have hG (y : E) (hy : y ∈ K) : ContDiffAt ℝ ∞ G y :=
    (g.contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (hKt hy))
  have hDG : ContinuousOn (fderiv ℝ G) K := fun y hy =>
    ((hG y hy).fderiv_right (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hGamma : ContinuousOn Gamma K := fun y hy =>
    (contDiffAt_christoffelBilinear (hG y hy)
      (g.isInvertible_chartCoefficients p (hKt hy))).continuousAt.continuousWithinAt
  obtain ⟨J0, hJ0⟩ := hK.exists_bound_of_continuousOn hDG
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hGamma
  obtain ⟨A0, hA0⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  let J := max J0 0
  let C := max C0 0
  let A := max D (max A0 0)
  let F := 2 * C * D ^ 2 + (2 * J * D ^ 2 / kappa + 2 * L * N * D)
  have hJ : 0 ≤ J := le_max_right _ _
  have hC : 0 ≤ C := le_max_right _ _
  have hJB (y : E) (hy : y ∈ K) : ‖fderiv ℝ G y‖ ≤ J :=
    (hJ0 y hy).trans (le_max_left _ _)
  have hCB (y : E) (hy : y ∈ K) : ‖Gamma y‖ ≤ C :=
    (hC0 y hy).trans (le_max_left _ _)
  let Q := fun j x => ∑ i : Fin 2, G (u j x) (fderiv ℝ (u j) x (b i))
    (fderiv ℝ (u j) x (b i))
  let den := fun j x => (rho j) ^ 2 * lambda j x + Q j x
  have hQ (j x) (hx : x ∈ Metric.ball center R) : 0 ≤ Q j x := by
    apply Finset.sum_nonneg
    intro i _
    exact (mul_nonneg hkappa.le (sq_nonneg _)).trans (hcoer _ (hrange j hx) _)
  have hd (j x) (hx : x ∈ Metric.ball center R) : 0 < den j x := by
    have := hrho j
    have := (hl j x hx).1
    have := hQ j x hx
    dsimp only [den]
    positivity
  have hden (j x) (hx : x ∈ Metric.ball center R) : Q j x ≤ den j x := by
    exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (hl j x hx).1.le)
  refine ⟨A, F, hD.trans (le_max_left _ _), by dsimp [F]; positivity, ?_, ?_, ?_⟩
  · intro j x hx
    exact ⟨(hA0 _ (hrange j hx)).trans ((le_max_left _ _).trans (le_max_right _ _)),
      fun i => (hgrad j x hx i).trans (le_max_left _ _)⟩
  · intro j x hx
    have h := suAlphaLowerTerm_bound (Gamma (u j x)) (G (u j x))
      (fderiv ℝ G (u j x)) (fun i => fderiv ℝ (u j) x (b i))
      (fun i => fderiv ℝ (lambda j) x (b i)) (hl j x hx).1 (hd j x hx) (hc0 j)
      hkappa (hCB _ (hrange j hx)) (hJB _ (hrange j hx)) (hcoer _ (hrange j hx))
      (hden j x hx) (hgrad j x hx) (hl j x hx).2 (hdl j x hx)
    change ‖suNormalizedAlphaCoordinateSource g p (u j) (lambda j) (rho j) (c j) x‖ ≤ _ at h
    apply h.trans
    dsimp only [F]
    have hp : 0 ≤ 2 * J * D ^ 2 / kappa + 2 * L * N * D := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (hc1 j) hp]
  · intro delta hdelta
    have ht : Tendsto (fun j => c j * (4 * B / kappa)) atTop (𝓝 0) := by
      simpa using hc.mul_const (4 * B / kappa)
    filter_upwards [ht.eventually (gt_mem_nhds hdelta)] with j hj
    intro x hx
    have hux := (hu j).contDiffAt (Metric.isOpen_ball.mem_nhds hx)
    have hsym (v w : E) : G (u j x) v w = G (u j x) w v := g.symm _ _ _
    have hpos (v : E) : 0 ≤ G (u j x) v v :=
      (mul_nonneg hkappa.le (sq_nonneg _)).trans (hcoer _ (hrange j hx) _)
    have he := suAlphaEquation_nearLaplacian Gamma G (u j) (lambda j) x
      (hux.of_le (WithTop.coe_le_coe.mpr le_top))
      ((hG _ (hrange j hx)).differentiableAt (by simp))
      (((hlambda j).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      (hl j x hx).1 (hrho j) hsym hpos (heq j x hx)
    change (∑ i : Fin 2, suCoordinateHessian (u j) x i i) + c j •
      suAlphaHessianTerm (G (u j x)) (fun i => fderiv ℝ (u j) x (b i))
        (suCoordinateHessian (u j) x) (den j x) =
      suNormalizedAlphaCoordinateSource g p (u j) (lambda j) (rho j) (c j) x at he
    have hb := suAlphaHessianTerm_bound (G (u j x)) (fun i => fderiv ℝ (u j) x (b i))
      (suCoordinateHessian (u j) x) (hd j x hx) hkappa (hGB _ (hrange j hx))
      (hcoer _ (hrange j hx)) (hden j x hx)
    rw [← he, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (hc0 j)]
    calc
      _ ≤ c j * ((4 * B / kappa) * Real.sqrt
          (∑ i : Fin 2, ∑ k : Fin 2, ‖suCoordinateHessian (u j) x i k‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hb (hc0 j)
      _ ≤ delta * Real.sqrt
          (∑ i : Fin 2, ∑ k : Fin 2, ‖suCoordinateHessian (u j) x i k‖ ^ 2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hj.le (Real.sqrt_nonneg _)

end PoincareConjecture.M60
