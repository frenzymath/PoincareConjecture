import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.GradientTime
import Mathlib.Analysis.Normed.Operator.NNNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

open RicciFlowAnalysis

theorem scalarGradientNorm_eq_sqrt_scalarGradientSq
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (x : M) :
    scalarGradientNorm g D x = Real.sqrt (scalarGradientSq g D.scalarCurvature x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  have hsup : scalarGradientNorm g D x = ‖mvfderiv (𝓡 3) D.scalarCurvature x‖ := by
    rw [← ContinuousLinearMap.sSup_sphere_eq_norm]
    apply congrArg sSup
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v.1, ?_, Real.norm_eq_abs _⟩
      rw [mem_sphere_zero_iff_norm, norm_eq_sqrt_real_inner]
      change Real.sqrt (g.inner x v.1 v.1) = 1
      rw [v.2, Real.sqrt_one]
    · rintro ⟨v, hv, rfl⟩
      have hv' : g.inner x v v = 1 := by
        change inner ℝ v v = 1
        rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp hv]
        norm_num
      exact ⟨⟨v, hv'⟩, (Real.norm_eq_abs _).symm⟩
  have hdual : InnerProductSpace.toDual ℝ (TangentSpace (𝓡 3) x)
      (D.gradient D.scalarCurvature x) = mvfderiv (𝓡 3) D.scalarCurvature x := by
    ext v
    exact D.inner_gradient D.scalarCurvature x v
  rw [hsup, ← hdual, LinearIsometryEquiv.norm_map, norm_eq_sqrt_real_inner]
  exact congrArg Real.sqrt (D.gradient_normSq_eq_sum_mvfderiv_sq D.scalarCurvature x)

namespace RicciFlowAnalysis

theorem continuousOn_flow_timeDependentScalarGradientSq
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (G : RicciFlow n M J) {U : Set M}
    {q : ℝ × M → ℝ} (hU : IsOpen U)
    (hq : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ q (J ×ˢ U)) :
    ContinuousOn (fun p : ℝ × M =>
      scalarGradientSq (G.metric p.1) (fun y => q (p.1, y)) p.2) (J ×ˢ U) := by
  classical
  let B : (p : ℝ × M) → MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 n) p.2) ℝ :=
    fun p => MultilinearMap.mk' (R := ℝ)
      (fun v => mvfderiv (𝓡 n) (fun y => q (p.1, y)) p.2 (v 0) *
        mvfderiv (𝓡 n) (fun y => q (p.1, y)) p.2 (v 1))
      (by
        intro v i a b
        fin_cases i <;> simp [Function.update, map_add, add_mul, mul_add])
      (by
        intro v i c a
        fin_cases i <;> simp [Function.update, map_smul, smul_eq_mul, mul_assoc, mul_left_comm])
  have htrace := continuousOn_flow_tensorTrace G hU B (by
    intro V hV hVU X Y hX hY
    exact ((contMDiffOn_mvfderiv_spatial hV
      (hq.mono (prod_mono subset_rfl hVU)) hX).mul
      (contMDiffOn_mvfderiv_spatial hV
        (hq.mono (prod_mono subset_rfl hVU)) hY)).continuousOn)
  simpa only [scalarGradientSq, B, MultilinearMap.mk'_apply, pow_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using htrace

end RicciFlowAnalysis

namespace RicciFlow

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {J : Set ℝ}

theorem continuousOn_scalarGradientNorm (G : RicciFlow 3 M J) :
    ContinuousOn (fun p : ℝ × M =>
      scalarGradientNorm (G.metric p.1) (G.connection p.1) p.2) (J ×ˢ univ) := by
  have h := (RicciFlowAnalysis.continuousOn_flow_timeDependentScalarGradientSq G
    isOpen_univ G.contMDiffOn_scalarCurvature).sqrt
  simpa only [scalarGradientNorm_eq_sqrt_scalarGradientSq] using h

theorem tendstoUniformlyOn_scalarGradientNorm (G : RicciFlow 3 M J)
    {T : ℝ} (hT : T ∈ J) {A : Set M} (hA : IsCompact A) :
    TendstoUniformlyOn
      (fun t x => scalarGradientNorm (G.metric t) (G.connection t) x)
      (fun x => scalarGradientNorm (G.metric T) (G.connection T) x) (𝓝[J] T) A := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨V, hV, hbound⟩ := hA.mem_uniformity_of_prod
    (f := fun t x => scalarGradientNorm (G.metric t) (G.connection t) x)
    (G.continuousOn_scalarGradientNorm.mono (prod_mono subset_rfl (subset_univ A)))
    hT (Metric.dist_mem_uniformity hε)
  filter_upwards [hV] with t ht x hx
  have hb : dist (scalarGradientNorm (G.metric t) (G.connection t) x)
      (scalarGradientNorm (G.metric T) (G.connection T) x) < ε := hbound t ht x hx
  rwa [dist_comm] at hb

end RicciFlow

end PoincareConjecture
