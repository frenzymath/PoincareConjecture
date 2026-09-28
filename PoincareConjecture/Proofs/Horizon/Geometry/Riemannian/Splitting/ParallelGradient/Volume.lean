import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume.Measure
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume.Balls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

section Product

variable {n : ℕ} {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
  [T3Space N] [T3Space M] [MeasurableSpace N] [BorelSpace N]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 (n + 1)) ∞ M]
  (h : RiemannianMetric n N) (g : RiemannianMetric (n + 1) M)
  (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
  (hmetric : ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
    g.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
        h.inner z.1 v.1 w.1 + v.2 * w.2)

include hmetric

theorem volumeMeasure_ball_le_productIsometry (y : N) (r : ℝ) (hr : 0 < r) :
    g.volumeMeasure (g.ball (e (y, 0)) r) ≤
      ENNReal.ofReal (2 * r) * h.volumeMeasure (h.ball y r) := by
  have hp := measurePreserving_productIsometry h g e hmetric
  rw [← hp.measure_preimage_emb e.toHomeomorph.measurableEmbedding]
  calc
    (h.volumeMeasure.prod volume) (e ⁻¹' g.ball (e (y, 0)) r) ≤
        (h.volumeMeasure.prod volume) (h.ball y r ×ˢ Ioo (-r) r) :=
      measure_mono (productIsometry_preimage_ball_subset g h e hmetric y r hr)
    _ = _ := by
      rw [Measure.prod_prod, Real.volume_Ioo, show r - -r = 2 * r by ring, mul_comm]

theorem volumeMeasure_factor_lower_bound (y : N) (r κ : ℝ) (hr : 0 < r)
    (hlower : ENNReal.ofReal (κ * r ^ (n + 1)) ≤
      g.volumeMeasure (g.ball (e (y, 0)) r)) :
    ENNReal.ofReal ((κ / 2) * r ^ n) ≤ h.volumeMeasure (h.ball y r) := by
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < 2 * r)) ENNReal.ofReal_ne_top).mp
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * r),
    show 2 * r * (κ / 2 * r ^ n) = κ * r ^ (n + 1) by rw [pow_succ]; ring]
  exact hlower.trans (volumeMeasure_ball_le_productIsometry h g e hmetric y r hr)

end Product

theorem exists_parallelGradient_volumeSplitting
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] {g : RiemannianMetric (n + 1) M}
    {D : LeviCivitaData g} {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    Nonempty (zeroLevelSet f) ∧ ConnectedSpace (zeroLevelSet f) ∧ MetricComplete h ∧
    ∃ Φ : ℝ → M → M,
      ∃ e : (zeroLevelSet f × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M,
        (∀ x, Φ 0 x = x) ∧
        (∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f)) ∧
        (∀ z, e z = Φ z.2 (zeroLevelIncl f z.1)) ∧
        (∀ (z : zeroLevelSet f × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
          g.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
            (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
              h.inner z.1 v.1 w.1 + v.2 * w.2) ∧
        MeasurePreserving e (h.volumeMeasure.prod volume) g.volumeMeasure ∧
        (∀ y r, 0 < r →
          g.volumeMeasure (g.ball (e (y, 0)) r) ≤
            ENNReal.ofReal (2 * r) * h.volumeMeasure (h.ball y r)) ∧
        (∀ κ : ℝ, 0 < κ →
          (∀ y r, 0 < r → ENNReal.ofReal (κ * r ^ (n + 1)) ≤
            g.volumeMeasure (g.ball (e (y, 0)) r)) →
          ∀ y r, 0 < r → ENNReal.ofReal ((κ / 2) * r ^ n) ≤
            h.volumeMeasure (h.ball y r)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  obtain ⟨hne, hconn, hcomplete, Φ, e, h0, hΦ, _, he, _, hmetric, _, _⟩ :=
    exists_parallelGradient_productIsometry hc hf hu hz
  let : ConnectedSpace (zeroLevelSet f) := hconn
  let : SecondCountableTopology (zeroLevelSet f) := h.secondCountableTopology
  refine ⟨hne, hconn, hcomplete, Φ, e, h0, hΦ, he, hmetric,
    measurePreserving_productIsometry h g e hmetric,
    volumeMeasure_ball_le_productIsometry h g e hmetric, ?_⟩
  intro κ _ hlower y r hr
  exact volumeMeasure_factor_lower_bound h g e hmetric y r κ hr (hlower y r hr)

end PoincareConjecture.RiemannianMetric
