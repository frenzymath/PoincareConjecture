import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Differential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.CutTime





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace Poincare.VolumeComparison.Conjugate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem isInvertible_on_nonterminal_of_extension
    (g : PoincareConjecture.RiemannianMetric n M) (p : M) {R : ℝ}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (h : ∀ v ∈ Metric.ball 0 R,
      (v = 0 ∨ (v ≠ 0 ∧ ∃ q : ℝ, 1 < q ∧ q * ‖v‖ < R ∧
        g.edist p (e (q • v)) = ENNReal.ofReal (q * ‖v‖))) →
      (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible) :
    ∀ v ∈ localMinimizingSet (fun w => g.edist p (e w)) R \
      terminalRadialPoints (localMinimizingSet (fun w => g.edist p (e w)) R) R,
      (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
  intro v hv
  apply h v hv.1.1
  by_cases hv0 : v = 0
  · exact Or.inl hv0
  right
  refine ⟨hv0, ?_⟩
  obtain ⟨q, hq, hqR, hqS⟩ : ∃ q : ℚ, 1 < (q : ℝ) ∧ (q : ℝ) * ‖v‖ < R ∧
      (q : ℝ) • v ∈ localMinimizingSet (fun w => g.edist p (e w)) R := by
    by_contra hnone
    apply hv.2
    refine ⟨hv.1, hv0, mem_iInter.mpr ?_⟩
    intro q hq
    exact hnone ⟨q, hq⟩
  refine ⟨q, hq, hqR, ?_⟩
  simpa only [mem_ofPred_eq, norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ (q : ℝ))]
    using hqS.2

end Poincare.VolumeComparison.Conjugate
