import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessLocalEstimate
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerGradientModulus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

noncomputable section

universe u

namespace PoincareConjecture.M60

local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

theorem suSmooth_weak_columns {m : ℕ} (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ ∞ u) {O : Set LoopPlane} (hO : IsOpen O) (i : Fin 2) (a : Fin m) :
    HasWeakPartialDeriv i (fun x => (fderiv ℝ u x (b i)) a) (fun x => u x a) O := by
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := EuclideanSpace.proj a
  have hc : ContDiff ℝ 1 (fun x => u x a) := L.contDiff.comp (hu.of_le (by simp))
  have hd : (fun x => fderiv ℝ (fun y => u y a) x (EuclideanSpace.single i 1)) =
      fun x => (fderiv ℝ u x (b i)) a := by
    funext x
    change fderiv ℝ (L ∘ u) x (EuclideanSpace.single i 1) = L (fderiv ℝ u x (b i))
    rw [(L.hasFDerivAt.comp x ((hu.differentiable (by simp)) x).hasFDerivAt).fderiv]
    simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.basisFun_apply]
  have h := HasWeakPartialDeriv.of_contDiff (i := i) (Ω := O) hO hc
  rwa [hd] at h

theorem suSmooth_nearLaplacian_gradient_modulus :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧ ∀ (m : ℕ) (D F : ℝ), 0 ≤ D → 0 ≤ F →
      ∀ (u f : LoopPlane → EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ∞ u → ContinuousOn f (Metric.ball 0 2) →
      (∀ x ∈ Metric.ball (0 : LoopPlane) 2, ‖u x‖ ≤ D ∧
        ∀ i : Fin 2, ‖fderiv ℝ u x (b i)‖ ≤ D) →
      (∀ x ∈ Metric.ball (0 : LoopPlane) 2, ‖f x‖ ≤ F) →
      (∀ x ∈ Metric.ball (0 : LoopPlane) 2,
        ‖(∑ i : Fin 2, suCoordinateHessian u x i i) - f x‖ ≤
          delta * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖suCoordinateHessian u x i j‖ ^ 2)) →
      ∀ i, ∀ x ∈ Metric.closedBall (0 : LoopPlane) (1 / 4),
        ∀ y ∈ Metric.closedBall (0 : LoopPlane) (1 / 4),
        ‖fderiv ℝ u x (b i) - fderiv ℝ u y (b i)‖ ≤
          C * (D + F) * Real.sqrt (Real.sqrt (dist x y)) := by
  obtain ⟨delta, C, hdelta, hC, hmod⟩ := suNearLaplacian_gradient_modulus
  refine ⟨delta, C, hdelta, hC, ?_⟩
  intro m D F hD hF u f hu hf hjet hsource hres
  let mu := volume.restrict (Metric.ball (0 : LoopPlane) 2)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  let p := fun i x => fderiv ℝ u x (b i)
  let H := fun i j x => suCoordinateHessian u x i j
  have hp (i : Fin 2) : ContDiff ℝ ∞ (p i) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hH (i j : Fin 2) : Continuous (H i j) :=
    ((hp i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hm (v : LoopPlane → EuclideanSpace ℝ (Fin m)) (hv : Continuous v) :
      MemLp v 2 mu := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : LoopPlane) 2).exists_bound_of_continuousOn
      hv.continuousOn
    apply MemLp.of_bound hv.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hB x (Metric.ball_subset_closedBall hx)
  have hfm : MemLp f 4 mu := by
    apply MemLp.of_bound (hf.aestronglyMeasurable Metric.isOpen_ball.measurableSet) F
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hsource x hx
  intro i x hx y hy
  exact hmod m D F hD hF (hm u hu.continuous) (fun i => hm _ (hp i).continuous)
    (suSmooth_weak_columns u hu Metric.isOpen_ball) (fun i j => hm _ (hH i j))
    (fun i j a => suSmooth_weak_columns (p i) (hp i) Metric.isOpen_ball j a)
    hfm (fun i => (hp i).continuous.continuousOn) (fun x hx => (hjet x hx).1)
    (fun i x hx => (hjet x hx).2 i) hsource hres i x hx y hy

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance suCompactHolderBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactHolderBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suCompactHolderTrilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactHolderTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suCompactHolderChristoffelNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactHolderChristoffelNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

theorem suNormalizedAlphaCoordinateSource_continuousOn
    (g : RiemannianMetric n M) (p : M) (u : LoopPlane → E) (lambda : LoopPlane → ℝ)
    {O : Set LoopPlane} (_hO : IsOpen O) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) p).target)
    (hu : ContDiff ℝ ∞ u) (hlambda : ContDiff ℝ ∞ lambda)
    (hrange : MapsTo u O K) (hpos : ∀ x ∈ O, 0 < lambda x)
    {rho : ℝ} (hrho : 0 < rho) (c : ℝ) :
    ContinuousOn (suNormalizedAlphaCoordinateSource g p u lambda rho c) O := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  let Gamma := CoordinateExponential.christoffelBilinear G
  let V := fun i x => fderiv ℝ u x (b i)
  let Q := fun x => ∑ i : Fin 2, G (u x) (V i x) (V i x)
  let den := fun x => rho ^ 2 * lambda x + Q x
  obtain ⟨kappa, _, hkappa, _, _, _, hcoer⟩ := suAlpha_coordinate_metric_bounds g p hK hKt
  have hV (i : Fin 2) : Continuous (V i) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdl (i : Fin 2) : Continuous (fun x => fderiv ℝ lambda x (b i)) :=
    (hlambda.continuous_fderiv (by simp)).clm_apply continuous_const
  intro x hx
  have hG : ContDiffAt ℝ ∞ G (u x) :=
    (g.contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (hKt (hrange hx)))
  have hGc : ContinuousAt (fun y => G (u y)) x := hG.continuousAt.comp (hu.continuous.continuousAt)
  have hDGc : ContinuousAt (fun y => fderiv ℝ G (u y)) x :=
    (hG.fderiv_right (m := ∞) (by simp)).continuousAt.comp (hu.continuous.continuousAt)
  have hGamma : ContinuousAt (fun y => Gamma (u y)) x :=
    (CoordinateExponential.contDiffAt_christoffelBilinear hG
      (g.isInvertible_chartCoefficients p (hKt (hrange hx)))).continuousAt.comp
        (hu.continuous.continuousAt)
  have hQ : ContinuousAt Q x := by
    dsimp only [Q]
    exact tendsto_finsetSum _ (fun i _ => (hGc.clm_apply (hV i).continuousAt).clm_apply
      (hV i).continuousAt)
  have hQ0 : 0 ≤ Q x := Finset.sum_nonneg fun i _ =>
    (mul_nonneg hkappa.le (sq_nonneg _)).trans (hcoer _ (hrange hx) _)
  have hd : 0 < den x := by
    have hlx := hpos x hx
    dsimp only [den]
    positivity
  have hdc : ContinuousAt den x := ((continuousAt_const.mul hlambda.continuous.continuousAt).add hQ)
  have hsum : ContinuousAt (fun y => ∑ i : Fin 2,
      ((∑ k : Fin 2, fderiv ℝ G (u y) (V i y) (V k y) (V k y)) -
        Q y * fderiv ℝ lambda y (b i) / lambda y) • V i y) x := by
    apply tendsto_finsetSum
    intro i _
    have htr : ContinuousAt (fun y => ∑ k : Fin 2,
        fderiv ℝ G (u y) (V i y) (V k y) (V k y)) x := by
      apply tendsto_finsetSum
      intro k _
      exact ((hDGc.clm_apply (hV i).continuousAt).clm_apply (hV k).continuousAt).clm_apply
        (hV k).continuousAt
    exact (htr.sub ((hQ.mul (hdl i).continuousAt).div hlambda.continuous.continuousAt
      (hpos x hx).ne')).smul (hV i).continuousAt
  have hconnection : ContinuousAt (fun y => ∑ i : Fin 2, Gamma (u y) (V i y) (V i y)) x := by
    exact tendsto_finsetSum _ (fun i _ =>
      (hGamma.clm_apply (hV i).continuousAt).clm_apply (hV i).continuousAt)
  exact (hconnection.neg.sub ((continuousAt_const.div hdc hd.ne').smul hsum)).continuousWithinAt

end PoincareConjecture.M60
