import PoincareConjecture.Proofs.M35.Thm12_28.ScalarGradientConvergence
import PoincareConjecture.Proofs.M04.ScalarEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem scalarGradientNorm_eq_sqrt_scalarGradientSq
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M) :
    scalarGradientNorm g D x = Real.sqrt (M04.scalarGradientSq g D.scalarCurvature x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [scalarGradientNorm_eq_gradient_norm, RiemannianMetric.tangentNorm]
  congr 1
  simp only [M04.scalarGradientSq, ← D.inner_gradient]
  change inner ℝ (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) =
    ∑ i, (inner ℝ (D.gradient D.scalarCurvature x) (g.orthonormalBasis x i)) ^ 2
  rw [real_inner_self_eq_norm_sq, OrthonormalBasis.sum_sq_inner_left]

theorem continuousOn_flow_scalarGradientNorm {J : Set ℝ} (F : RicciFlow 3 M J) :
    ContinuousOn (fun p : ℝ × M => scalarGradientNorm (F.metric p.1)
      (F.connection p.1) p.2) (J ×ˢ univ) := by
  classical
  let q := fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2
  let T : (p : ℝ × M) → MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 3) p.2) ℝ :=
    fun p => MultilinearMap.mk' (R := ℝ)
      (fun v => mvfderiv (𝓡 3) (fun y => q (p.1, y)) p.2 (v 0) *
        mvfderiv (𝓡 3) (fun y => q (p.1, y)) p.2 (v 1))
      (by
        intro v i a b
        fin_cases i <;> simp [Function.update, map_add, add_mul, mul_add])
      (by
        intro v i c a
        fin_cases i <;> simp [Function.update, map_smul, smul_eq_mul, mul_assoc, mul_left_comm])
  have htrace := M04.continuousOn_flow_tensorTrace F isOpen_univ T (by
    intro V hV hVU X Y hX hY
    have hq := F.contMDiffOn_scalarCurvature.mono (prod_mono Subset.rfl hVU)
    exact ((M04.contMDiffOn_mvfderiv_spatial hV hq hX).mul
      (M04.contMDiffOn_mvfderiv_spatial hV hq hY)).continuousOn)
  have hsquare : ContinuousOn (fun p : ℝ × M =>
      M04.scalarGradientSq (F.metric p.1) (F.connection p.1).scalarCurvature p.2)
      (J ×ˢ univ) := by
    simpa only [M04.scalarGradientSq, T, q, MultilinearMap.mk'_apply, pow_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using htrace
  convert! hsquare.sqrt using 1
  ext p
  exact scalarGradientNorm_eq_sqrt_scalarGradientSq (F.connection p.1) p.2

theorem continuousOn_flow_scalar_evolution [T2Space M]
    {J : Set ℝ} (F : RicciFlow 3 M J) :
    ContinuousOn (fun p : ℝ × M =>
      (F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2 +
        2 * (F.connection p.1).ricciNormSq p.2) (J ×ˢ univ) :=
  (M04.continuousOn_flow_timeDependentLaplacian F F.contMDiffOn_scalarCurvature).add
    (continuousOn_const.mul (M04.continuousOn_flow_ricciNormSq F))

end PoincareConjecture.M35
