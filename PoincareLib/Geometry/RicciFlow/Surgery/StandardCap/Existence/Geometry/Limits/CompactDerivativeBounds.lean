import PoincareLib.Geometry.RicciFlow.Curvature.Theory

/-!
# Global compact initial derivative estimates on a closed slab

The M04 initial derivative estimate with equal initial and target orders
has zero time exponent. Centering its fixed-radius ball at each point
gives one global bound including time zero. The constant precedes the
manifold and flow. This is the endpoint estimate in Morgan-Tian
Theorem 12.5, p. 297; see the common-compact-lifetime derivation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal
open Set

universe u

namespace PoincareMT.M34

/-- Uniform initial derivatives through order k and full-curvature control
give one order-k bound on the entire compact slab (Theorem 12.5, p. 297). -/
theorem compact_initial_derivative_bound (P : RicciFlowCurvatureTheory.{u})
    (n k : ℕ) {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M]
      (F : RicciFlow n M (Icc 0 T)),
      (∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) →
      (∀ j ≤ k, ∀ x : M, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
      ∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨C, hC, hest⟩ := P.initial_derivative_estimates n k k K (T * K) 1
    hK (mul_pos hT hK) zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ F hfull hinit t ht x
  have htime : T ≤ T * K / K := by rw [mul_div_cancel_right₀ T (ne_of_gt hK)]
  have hself : (F.metric 0).edist x x = 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_self
  have hx : x ∈ (F.metric 0).ball x (1 / 2) := by
    change (F.metric 0).edist x x < ENNReal.ofReal (1 / 2)
    rw [hself]
    norm_num
  have h := hest M T hT htime F x isClosed_closure.isCompact
    hfull hinit t ht (Or.inr le_rfl) x hx
  simpa only [Nat.sub_self, Nat.cast_zero, zero_div, Real.rpow_zero, div_one] using h

end PoincareMT.M34
