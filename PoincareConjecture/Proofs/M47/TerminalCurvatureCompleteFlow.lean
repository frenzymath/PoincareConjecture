import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Global
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Flow.LinearGrowth










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47



theorem terminalCurvature_complete_unit_flow
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hg : MetricComplete g)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hunit : ∀ x, g.inner x (V x) (V x) = 1) :
    ∃ Phi : ℝ → M → M,
      (∀ x, Phi 0 x = x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun tx : ℝ × M => Phi tx.1 tx.2) ∧
      (∀ x, IsMIntegralCurve (fun t => Phi t x) V) ∧
      ∀ s t x, Phi (s + t) x = Phi s (Phi t x) := by
  have hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, V tx.2⟩ : TangentBundle (𝓡 n) M))
      ((univ : Set ℝ) ×ˢ univ) :=
    (hV.comp contMDiff_snd).contMDiffOn
  have hconf (x : M) (a b : ℝ) (hs : (0 : ℝ) ∈ Icc a b)
      (_ : Icc a b ⊆ (univ : Set ℝ)) :=
    g.exists_compact_confinement_of_linear_growth hg x x
      (X := fun _ => V) hs (show 0 ≤ (1 : ℝ) by norm_num)
      (fun _ _ y => by
        simp only [RiemannianMetric.tangentNorm, hunit, Real.sqrt_one, one_mul]
        exact le_add_of_nonneg_right ENNReal.toReal_nonneg)
  obtain ⟨Psi, hzero, hPsi⟩ :=
    Poincare.Manifold.exists_smooth_timeDependentFlow_from_anchor_of_compact_confinement
      isOpen_univ (convex_univ : Convex ℝ (univ : Set ℝ)) hX (mem_univ (0 : ℝ)) hconf
  let Phi : ℝ → M → M := fun t x => Psi (t, x)
  have hcurve (x : M) : IsMIntegralCurve (fun t => Phi t x) V :=
    fun t => hPsi.orbit x (mem_univ x) t (mem_univ t)
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun tx : ℝ × M => Phi tx.1 tx.2) := by
    apply contMDiffOn_univ.mp
    simpa only [univ_prod_univ] using hPsi.smooth
  refine ⟨Phi, hzero, hsmooth, hcurve, ?_⟩
  intro s t x
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (hV.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
    ((hcurve x).comp_add t) (hcurve (Phi t x)) (t₀ := 0)
    (by simpa only [Function.comp_apply, zero_add] using (hzero (Phi t x)).symm)
  exact congrFun heq s

end PoincareConjecture.M47
