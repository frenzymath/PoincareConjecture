import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper

/-!
# Uniform initial derivative estimates from initial completeness

The initial metric's closed balls are compact. The equal-order Shi estimate
has zero time exponent and a constant chosen before the shorter time slab.
This is the complete-flow derivative step in Morgan-Tian Theorem 12.5,
p. 297; see the reviewed maximal-continuation-restart derivation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M34

/-- Initial completeness, bounded curvature, and bounded initial
derivatives give uniform closed-slab derivative bounds, with the constant
chosen before the slab length (Theorem 12.5, p. 297). -/
theorem complete_initial_derivative_bound (P : RicciFlowCurvatureTheory.{u})
    (n k : ℕ) {K S : ℝ} (hK : 0 < K) (hS : 0 < S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (T : ℝ), 0 < T → T ≤ S → ∀ (F : RicciFlow n M (Icc 0 T)),
      MetricComplete (F.metric 0) →
      (∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) →
      (∀ j ≤ k, ∀ x : M, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
      ∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨C, hC, hest⟩ := P.initial_derivative_estimates n k k K (S * K) 1
    hK (mul_pos hS hK) zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ T hT hTS F hcomplete hfull hinit t ht x
  have htime : T ≤ S * K / K := by rwa [mul_div_cancel_right₀ S (ne_of_gt hK)]
  have hself : (F.metric 0).edist x x = 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_self
  have hx : x ∈ (F.metric 0).ball x (1 / 2) := by
    change (F.metric 0).edist x x < ENNReal.ofReal (1 / 2)
    rw [hself]
    norm_num
  have h := hest M T hT htime F x
    (PoincareMT.Proofs.M09.isCompact_closure_metric_ball _ hcomplete x 1)
    hfull hinit t ht (Or.inr le_rfl) x hx
  simpa only [Nat.sub_self, Nat.cast_zero, zero_div, Real.rpow_zero, div_one] using h

end PoincareMT.M34
