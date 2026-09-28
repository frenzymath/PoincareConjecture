import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Gradient
import Mathlib.Analysis.Normed.Operator.NNNorm










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture



theorem scalarGradientNorm_eq_tangentNorm
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (x : M) :
    scalarGradientNorm g D x = g.tangentNorm x (D.gradient D.scalarCurvature x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let L := innerSL ℝ (D.gradient D.scalarCurvature x)
  have heq : Set.range (fun v : {v : TangentSpace (𝓡 3) x // g.inner x v v = 1} =>
      |mvfderiv (𝓡 3) D.scalarCurvature x v.val|) =
      (fun v => ‖L v‖) '' Metric.sphere 0 1 := by
    ext r
    constructor
    · rintro ⟨⟨v, hv⟩, rfl⟩
      refine ⟨v, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm]
        change Real.sqrt (g.inner x v v) = 1
        rw [hv, Real.sqrt_one]
      · change ‖g.inner x (D.gradient D.scalarCurvature x) v‖ = _
        rw [Real.norm_eq_abs, D.inner_gradient]
    · rintro ⟨v, hv, rfl⟩
      have hunit : g.inner x v v = 1 := by
        change inner ℝ v v = 1
        rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp hv]
        norm_num
      refine ⟨⟨v, hunit⟩, ?_⟩
      change _ = ‖g.inner x (D.gradient D.scalarCurvature x) v‖
      rw [Real.norm_eq_abs, D.inner_gradient]
  change sSup _ = _
  rw [heq, L.sSup_sphere_eq_norm, innerSL_apply_norm]
  rfl

end PoincareConjecture
