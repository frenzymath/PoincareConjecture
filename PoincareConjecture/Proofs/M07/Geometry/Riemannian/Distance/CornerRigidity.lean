import Mathlib.Analysis.InnerProductSpace.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false





theorem eq_neg_of_norm_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u₁ u₂ : E} (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1)
    (hstep : ∀ θ : ℝ, 1 < θ → 2 ≤ θ * ‖u₂ - u₁‖) :
    u₂ = -u₁ := by
  have hdiff : 2 ≤ ‖u₂ - u₁‖ := by
    by_contra hlt
    push Not at hlt
    have hs : 0 ≤ ‖u₂ - u₁‖ := norm_nonneg _
    rcases eq_or_lt_of_le hs with hz | hz
    · linarith [hstep 2 one_lt_two]
    · let s : ℝ := ‖u₂ - u₁‖
      have hθ : 1 < (1 + 2 / s) / 2 := by
        have hdiv : 1 < 2 / s := (lt_div_iff₀ hz).2 (by nlinarith)
        nlinarith
      have hθlt : (1 + 2 / s) / 2 < 2 / s := by
        dsimp [s]
        nlinarith
      have hcontra := hstep ((1 + 2 / s) / 2) hθ
      have hprod : ((1 + 2 / s) / 2) * s < 2 := by
        calc
          _ < (2 / s) * s := mul_lt_mul_of_pos_right hθlt hz
          _ = 2 := by
            exact div_mul_cancel₀ 2 (show s ≠ 0 from ne_of_gt hz)
      dsimp [s] at hprod hcontra
      linarith
  have hQ4 : (4 : ℝ) ≤ @inner ℝ E _ (u₂ - u₁) (u₂ - u₁) := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [hdiff]
  have hexp1 : @inner ℝ E _ (u₂ - u₁) (u₂ - u₁) =
      2 - 2 * @inner ℝ E _ u₁ u₂ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm, h₁, h₂]
    ring
  have hexp2 : @inner ℝ E _ (u₁ + u₂) (u₁ + u₂) =
      2 + 2 * @inner ℝ E _ u₁ u₂ := by
    simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_comm, h₁, h₂]
    ring
  have hsum : @inner ℝ E _ (u₁ + u₂) (u₁ + u₂) ≤ 0 := by
    rw [hexp2]
    rw [hexp1] at hQ4
    linarith
  have hzero : u₁ + u₂ = 0 := by
    rw [real_inner_self_eq_norm_sq] at hsum
    exact norm_eq_zero.mp (by nlinarith [hsum, sq_nonneg ‖u₁ + u₂‖])
  exact eq_neg_of_add_eq_zero_right hzero

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem eq_neg_of_radial_edist_eq
    (g : RiemannianMetric n M) (p : M)
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hchord : ∀ θ : ℝ, 1 < θ → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ v w : EuclideanSpace ℝ (Fin n), ‖v‖ < ρ → ‖w‖ < ρ →
        g.edist (e v) (e w) ≤ ENNReal.ofReal (θ * g.tangentNorm p (w - v)))
    {u₁ u₂ : EuclideanSpace ℝ (Fin n)}
    (h₁ : g.tangentNorm p u₁ = 1) (h₂ : g.tangentNorm p u₂ = 1)
    {η₀ : ℝ} (hη₀ : 0 < η₀)
    (h : ∀ η : ℝ, 0 < η → η < η₀ →
      g.edist (e (η • u₁)) (e (η • u₂)) = ENNReal.ofReal (2 * η)) :
    u₂ = -u₁ := by
  have hstep : ∀ θ : ℝ, 1 < θ → 2 ≤ θ * g.tangentNorm p (u₂ - u₁) := by
    intro θ hθ
    obtain ⟨ρ, hρ, hρbound⟩ := hchord θ hθ
    let S := ‖u₁‖ + ‖u₂‖ + 1
    have hS : 0 < S := by dsimp [S]; positivity
    let η := min (η₀ / 2) (ρ / S)
    have hη : 0 < η := lt_min (by linarith) (div_pos hρ hS)
    have hηη₀ : η < η₀ := (min_le_left _ _).trans_lt (by linarith)
    have hsmall (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ < S) : ‖η • u‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      calc
        η * ‖u‖ ≤ (ρ / S) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hS]
          exact mul_lt_mul_of_pos_left hu hρ
    have hu₁ : ‖u₁‖ < S := by dsimp [S]; linarith [norm_nonneg u₂]
    have hu₂ : ‖u₂‖ < S := by dsimp [S]; linarith [norm_nonneg u₁]
    have hle := hρbound (η • u₁) (η • u₂) (hsmall u₁ hu₁) (hsmall u₂ hu₂)
    rw [h η hη hηη₀, ← smul_sub] at hle
    have hsmul : g.tangentNorm p (η • (u₂ - u₁)) =
        η * g.tangentNorm p (u₂ - u₁) := by
      unfold tangentNorm
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [show η * (η * g.inner p (u₂ - u₁) (u₂ - u₁)) =
        η ^ 2 * g.inner p (u₂ - u₁) (u₂ - u₁) by ring,
        Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le]
    rw [hsmul] at hle
    have hreal := (ENNReal.ofReal_le_ofReal_iff
      (show 0 ≤ θ * (η * g.tangentNorm p (u₂ - u₁)) by
        unfold tangentNorm; positivity)).mp hle
    nlinarith
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (v : TangentSpace (𝓡 n) p) : ‖v‖ = g.tangentNorm p v := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  exact @eq_neg_of_norm_lower_bound (TangentSpace (𝓡 n) p) _ _ u₁ u₂
    ((hnorm u₁).trans h₁) ((hnorm u₂).trans h₂)
    (by simpa only [hnorm] using! hstep)

end PoincareConjecture.RiemannianMetric
