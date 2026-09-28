import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.SelfSimilar.Variation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem hasDerivAt_selfSimilar_inner
    (S : GradientShrinkingSolitonData n M)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ S.potential) {Φ : ℝ → M → M}
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun z : ℝ × M => Φ z.1 z.2))
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (S.connection.gradient S.potential))
    (x : M) (v w : TangentSpace (𝓡 n) x) (t : ℝ) (ht : t < 0) :
    HasDerivAt (fun s => (-s) * S.metric.inner (Φ (-Real.log (-s)) x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-s))) x v)
      (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-s))) x w))
      (-2 * S.connection.ricci (Φ (-Real.log (-t)) x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-t))) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-t))) x w)) t := by
  have htime : HasDerivAt (fun s : ℝ => -Real.log (-s)) (-t)⁻¹ t := by
    convert! (((hasDerivAt_id t).neg).log (neg_ne_zero.mpr ht.ne)).neg using 1
    simp [div_eq_mul_inv]
  have hpair := RiemannianMetric.hasDerivAt_gradientFlow_metric_pairing
    hf hs hΦ x v w (-Real.log (-t))
  have hcomp := hpair.comp t htime
  have hmul := ((hasDerivAt_id t).neg).mul hcomp
  apply hmul.congr_deriv
  have hsol := S.soliton_equation (Φ (-Real.log (-t)) x)
    (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-t))) x v)
    (mfderiv (𝓡 n) (𝓡 n) (Φ (-Real.log (-t))) x w)
  simp only [Function.comp_apply, Pi.neg_apply, id_eq]
  rw [mul_left_comm (-t), mul_inv_cancel₀ (neg_ne_zero.mpr ht.ne), mul_one]
  linarith

end PoincareConjecture.GradientShrinkingSolitonData
