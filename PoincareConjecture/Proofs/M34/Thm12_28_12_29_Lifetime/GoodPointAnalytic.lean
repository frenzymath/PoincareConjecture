import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.GoodPoint
import PoincareConjecture.Proofs.M34.Standard.ScalarGradientNorm
import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionHomothety
import PoincareConjecture.Proofs.M04.ScalarEvolution











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M34



theorem chapter11GoodPoint_of_scalar_bounds
    {G : GeneralizedRicciFlowData.{u}} {epsilon C A : ℝ} (p : G.point)
    (hcanonical : Nonempty (GeneralizedCanonicalControl (F := G) p.1 p.2 epsilon C))
    (hgradient : scalarGradientNorm (G.metric p.1) (G.connection p.1) p.2 ≤
      A * (G.scalar p) ^ (3 / 2 : ℝ))
    (hevolution : |(G.connection p.1).laplacian (G.connection p.1).scalarCurvature p.2 +
      2 * (G.connection p.1).ricciNormSq p.2| ≤ A * (G.scalar p) ^ 2) :
    Chapter11GoodPoint G epsilon C A p := by
  refine ⟨hcanonical, ?_, ?_⟩
  · intro v hv
    have hnorm : (G.metric p.1).tangentNorm p.2 v = 1 := by
      change Real.sqrt ((G.metric p.1).inner p.2 v v) = 1
      rw [hv, Real.sqrt_one]
    have h := (G.connection p.1).abs_mvfderiv_le_gradient_norm
      (G.connection p.1).scalarCurvature p.2 v
    rw [hnorm, mul_one, ← scalarGradientNorm_eq_tangentNorm] at h
    exact h.trans hgradient
  · intro b ht x hx
    let B := G.box b
    change B.forward p.1 ht x = p.2 at hx
    have hmetric : ∀ y ∈ (univ : Set B.carrier.carrier), ∀ v w,
        (B.flow.metric p.1).inner y v w = 1 * (G.metric p.1).inner
          (B.forward p.1 ht y) (mfderiv (𝓡 3) (𝓡 3) (B.forward p.1 ht) y v)
          (mfderiv (𝓡 3) (𝓡 3) (B.forward p.1 ht) y w) := by
      intro y _ v w
      simpa only [one_mul] using (B.metric_pullback p.1 ht y v w).symm
    have hscalar := (B.flow.connection p.1).scalarCurvature_eq_of_local_homothety
      (G.connection p.1) (Q := 1) zero_lt_one isOpen_univ
      (B.forward_smooth p.1 ht).contMDiffOn hmetric (mem_univ x)
    have hrate := (B.flow.connection p.1).scalarEvolutionNumerator_eq_of_local_homothety
      (G.connection p.1) (Q := 1) zero_lt_one isOpen_univ
      (B.forward_smooth p.1 ht).contMDiffOn hmetric (mem_univ x)
    simp only [one_pow, div_one, hx] at hscalar hrate
    refine ⟨(B.flow.connection p.1).laplacian (B.flow.connection p.1).scalarCurvature x +
      2 * (B.flow.connection p.1).ricciNormSq x,
      B.flow.hasDerivWithinAt_scalarCurvature p.1 ht x, ?_⟩
    rw [hrate, hscalar]
    exact hevolution

end PoincareConjecture.M34
