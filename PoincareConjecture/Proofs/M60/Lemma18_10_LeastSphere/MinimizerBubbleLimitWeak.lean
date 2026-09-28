import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessWeakLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

theorem suC1_harmonic_weakCoordinate
    (g : RiemannianMetric n M) (p : M) (u : LoopPlane → E)
    (hu : ContDiff ℝ 1 u) (center : LoopPlane) {R : ℝ} (hR : 0 < R)
    (hrange : MapsTo u (Metric.closedBall center R) (extChartAt (𝓡 n) p).target)
    (hvar : ∀ phi : LoopPlane → E, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Metric.ball center R →
      IntegrableOn (suAlphaChartVariation g p 1 u
        (fun i y => fderiv ℝ u y (b i)) phi) (Metric.ball center R) ∧
      (∫ z in Metric.ball center R, suAlphaChartVariation g p 1 u
        (fun i y => fderiv ℝ u y (b i)) phi z) = 0) :
    SUWeakAlphaCoordinate g p 1 u (fun i y => fderiv ℝ u y (b i)) center R := by
  let mu := volume.restrict (Metric.ball center R)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hm (f : LoopPlane → E) (hf : Continuous f) : MemLp f 2 mu := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall center R).exists_bound_of_continuousOn hf.continuousOn
    apply MemLp.of_bound hf.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    exact hC z (Metric.ball_subset_closedBall hz)
  have hcolumn (i : Fin 2) : Continuous (fun y => fderiv ℝ u y (b i)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ⟨hR, hrange, hu.continuous.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [mul_one, ENNReal.ofReal_ofNat] using hm u hu.continuous
  · intro i
    simpa only [mul_one, ENNReal.ofReal_ofNat] using hm _ (hcolumn i)
  · intro i a
    let L : E →L[ℝ] ℝ := EuclideanSpace.proj a
    have hc : ContDiff ℝ 1 (fun y => u y a) := L.contDiff.comp hu
    have hd : (fun z => fderiv ℝ (fun y => u y a) z (EuclideanSpace.single i 1)) =
        fun z => (fderiv ℝ u z (b i)) a := by
      funext z
      change fderiv ℝ (L ∘ u) z (EuclideanSpace.single i 1) = L (fderiv ℝ u z (b i))
      rw [(L.hasFDerivAt.comp z (hu.differentiable_one z).hasFDerivAt).fderiv]
      simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.basisFun_apply]
    have hw := HasWeakPartialDeriv.of_contDiff (i := i) (Ω := Metric.ball center R)
      Metric.isOpen_ball hc
    rw [hd] at hw
    exact hw
  · intro phi hp hc hs
    exact (hvar phi hp hc hs).1
  · intro phi hp hc hs
    exact (hvar phi hp hc hs).2

end PoincareConjecture.M60
