import PoincareConjecture.Proofs.M10.IntrinsicLipschitz
import Mathlib.Analysis.Normed.Module.HahnBanach









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in

theorem edist_le_mul_riemannianEDist_of_vector_differential
    (g : RiemannianMetric n M) {f : M → E} {U : Set M}
    (hf : ContinuousOn f U) (hfd : ∀ q ∈ U,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) f q) {C : ℝ≥0}
    (hbound : ∀ q ∈ U, ∀ v : TangentSpace (𝓡 n) q,
      ‖mvfderiv (𝓡 n) f q v‖ ≤ C * g.tangentNorm q v)
    {x₀ x y : M} {r : ℝ≥0}
    (hball : ∀ q, g.edist x₀ q < (r : ℝ≥0∞) + r + r → q ∈ U)
    (hx : g.edist x₀ x < r) (hy : g.edist x₀ y < r) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * g.edist x y := by
  obtain ⟨ℓ, hℓ, heval⟩ := exists_dual_vector'' ℝ (f x - f y)
  rw [RCLike.ofReal_real_eq_id, id_eq] at heval
  have h := edist_le_mul_riemannianEDist_of_upper_supports g
    (ℓ.continuous.comp_continuousOn hf) (C := C) (fun q hq ↦ ?_) hball hx hy
  · have hdist : edist (ℓ (f x)) (ℓ (f y)) = edist (f x) (f y) := by
      rw [edist_dist, edist_dist, Real.dist_eq, dist_eq_norm, ← map_sub, heval,
        abs_of_nonneg (norm_nonneg _)]
    exact hdist ▸ h
  refine ⟨ℓ ∘ f, ℓ.differentiableAt.mdifferentiableAt.comp q (hfd q hq),
    rfl, Filter.Eventually.of_forall (fun _ ↦ le_rfl), ?_⟩
  intro v
  have hchain : mvfderiv (𝓡 n) (ℓ ∘ f) q v = ℓ (mvfderiv (𝓡 n) f q v) := by
    rw [mvfderiv_comp q ℓ.differentiableAt.mdifferentiableAt (hfd q hq)]
    simp only [mvfderiv, mfderiv_eq_fderiv, ℓ.fderiv,
      ContinuousLinearMap.comp_apply]
    rfl
  rw [hchain, ← Real.norm_eq_abs]
  exact (ℓ.le_opNorm _).trans <| calc
    ‖ℓ‖ * ‖mvfderiv (𝓡 n) f q v‖ ≤ 1 * ‖mvfderiv (𝓡 n) f q v‖ :=
      mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
    _ ≤ C * g.tangentNorm q v := by simpa only [one_mul] using hbound q hq v

end PoincareConjecture.M10
