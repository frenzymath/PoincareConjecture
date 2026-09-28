import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]


theorem edist_eq_of_metric_line_coordinate (g : RiemannianMetric 1 M)
    (e : M ≃ ℝ) (he : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) 1 e)
    (hi : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 1 e.symm)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 1) x),
      g.inner x v w = mvfderiv (𝓡 1) e x v * mvfderiv (𝓡 1) e x w)
    (x y : M) : EDist.edist (e x) (e y) = g.edist x y := by
  have hnorm (z : M) (v : TangentSpace (𝓡 1) z) :
      g.tangentNorm z v = |mvfderiv (𝓡 1) e z v| := by
    rw [tangentNorm, hmetric, Real.sqrt_mul_self_eq_abs]
  apply le_antisymm
  · simpa using g.edist_le_mul_edist_of_derivative_bound he
      (K := 1) (by norm_num)
      (fun z v => by simp [hnorm])
      x y
  · let l : ℝ → ℝ := fun t => e x + t * (e y - e x)
    let γ : ℝ → M := fun t => e.symm (l t)
    have hl : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 l := by
      apply ContDiff.contMDiff
      dsimp [l]
      fun_prop
    have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 1 γ := hi.comp hl
    have heq : e ∘ γ = l := by
      funext t
      exact e.apply_symm_apply (l t)
    have hvel (t : ℝ) :
        mvfderiv (𝓡 1) e (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t 1) = e y - e x := by
      have hc := congrArg (fun L => L 1) (mvfderiv_comp t
        (he.mdifferentiable one_ne_zero (γ t)) (hγ.mdifferentiable one_ne_zero t))
      have hd : HasDerivAt l (e y - e x) t := by
        simpa [l] using ((hasDerivAt_id t).mul_const (e y - e x)).const_add (e x)
      have hdl : mvfderiv 𝓘(ℝ, ℝ) l t 1 = e y - e x := by
        rw [mvfderiv, mfderiv_eq_fderiv]
        change fderiv ℝ l t 1 = e y - e x
        exact hd.deriv
      rw [heq] at hc
      exact hc.symm.trans hdl
    have hlength : g.pathELength γ 0 1 = EDist.edist (e x) (e y) := by
      rw [pathELength_eq_lintegral_tangentNorm]
      simp_rw [hnorm, hvel]
      simp [Real.volume_Icc, edist_dist, Real.dist_eq, abs_sub_comm]
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 1) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn
      (by simp [γ, l]) (by simp [γ, l]) zero_le_one).trans_eq hlength

end PoincareConjecture.RiemannianMetric
