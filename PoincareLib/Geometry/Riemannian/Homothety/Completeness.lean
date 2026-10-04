import PoincareLib.Geometry.Riemannian.Homothety.Length
import PoincareLib.Geometry.RicciFlow.Harnack.Basic
import Mathlib.Topology.UniformSpace.Equiv

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M13/Completeness.lean`,
revision `0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See `references/ricci-flow/mapher/rescaling-import.json`. -/

/-!
# Completeness under positive metric homothety

The distance formula supplies a uniform equivalence between the two actual
Riemannian emetrics. Completeness therefore concerns the selected metrics,
without any assumption that all point pairs have finite distance.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle NNReal ENNReal

namespace PoincareMT.Homothety

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T3Space N]

/-- Positive metric homothety preserves completeness in both directions. -/
theorem homothety_complete_iff (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) : MetricComplete h ↔ MetricComplete g := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  change CompleteSpace N ↔ CompleteSpace M
  let c : ℝ≥0 := ⟨Real.sqrt Q, Real.sqrt_nonneg Q⟩
  have hc : (c : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt Q) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    rw [hc]
    exact (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hQ)).ne'
  have hforward : LipschitzWith c f := by
    intro x y
    change h.edist (f x) (f y) ≤ (c : ℝ≥0∞) * g.edist x y
    rw [homothety_edist g h f Q hQ hf, hc]
  have hinverse : LipschitzWith c⁻¹ f.symm := by
    intro x y
    change g.edist (f.symm x) (f.symm y) ≤ ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * h.edist x y
    have heq := homothety_edist g h f Q hQ hf (f.symm x) (f.symm y)
    rw [f.apply_symm_apply, f.apply_symm_apply, ← hc] at heq
    rw [ENNReal.coe_inv (ENNReal.coe_ne_zero.1 hc0), heq,
      ENNReal.inv_mul_cancel_left hc0 ENNReal.coe_ne_top]
  let e : M ≃ᵤ N :=
    { f.toEquiv with
      uniformContinuous_toFun := hforward.uniformContinuous
      uniformContinuous_invFun := hinverse.uniformContinuous }
  exact e.completeSpace_iff.symm

end PoincareMT.Homothety
