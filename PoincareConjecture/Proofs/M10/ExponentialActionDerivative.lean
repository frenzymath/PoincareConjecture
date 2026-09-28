import PoincareConjecture.Proofs.M10.ExponentialDifferential
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponential_action_fderiv (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y ↦ G.toLExponentialFamily.action (metricCoordinates (F.metric T) p y) τ) x v =
      2 * Real.sqrt τ * (F.metric (T - τ)).inner
        (G.gamma (metricCoordinates (F.metric T) p x) τ)
        (curveVelocity (G.gamma (metricCoordinates (F.metric T) p x)) τ)
        (G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
          (metricCoordinates (F.metric T) p v)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := (metricCoordinates (F.metric T) p).toContinuousLinearEquiv
  let A := fun Z ↦ G.toLExponentialFamily.action Z τ
  have hbase : DifferentiableAt ℝ
      (fun z : TangentSpace (𝓡 n) p × ℝ ↦ G.toLExponentialFamily.action z.1 z.2)
      (β x, τ) := (G.action_smooth.contDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hτ, hmax⟩)).differentiableAt
          (by simp)
  have hmap : DifferentiableAt ℝ (fun Z : TangentSpace (𝓡 n) p ↦ (Z, τ)) (β x) :=
    differentiableAt_id.prodMk (differentiableAt_const τ)
  have hA' := hbase.comp (f := fun Z : TangentSpace (𝓡 n) p ↦ (Z, τ)) (β x) hmap
  have hA : DifferentiableAt ℝ A (β x) := hA'
  change fderiv ℝ (A ∘ β) x v = _
  rw [fderiv_comp x hA β.differentiableAt, β.fderiv]
  exact G.action_initial_differential (β x) τ hτ hmax (β v)

set_option backward.isDefEq.respectTransparency false in

theorem exponential_velocity_pairing_of_quadratic_action
    (G : LExponentialGeometry F T τmax p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (ha : ∀ y : EuclideanSpace ℝ (Fin n),
      G.toLExponentialFamily.action (metricCoordinates (F.metric T) p y) τ /
        (2 * Real.sqrt τ) = ‖y‖ ^ 2) (x v : EuclideanSpace ℝ (Fin n)) :
    (F.metric (T - τ)).inner (G.gamma (metricCoordinates (F.metric T) p x) τ)
      (curveVelocity (G.gamma (metricCoordinates (F.metric T) p x)) τ)
      (G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
        (metricCoordinates (F.metric T) p v)) = 2 * inner ℝ x v := by
  have hne : 2 * Real.sqrt τ ≠ 0 := mul_ne_zero (by norm_num) (Real.sqrt_pos.2 hτ).ne'
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) ↦
      G.toLExponentialFamily.action (metricCoordinates (F.metric T) p y) τ) =
      (fun y ↦ (2 * Real.sqrt τ) * ‖y‖ ^ 2) := by
    funext y
    exact ((div_eq_iff hne).mp (ha y)).trans (mul_comm _ _)
  have hd := exponential_action_fderiv G hτ hmax x v
  rw [hfun, ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (2 * Real.sqrt τ)).fderiv]
    at hd
  have hv : ((2 * Real.sqrt τ) • (2 • innerSL ℝ x)) v =
      (2 * Real.sqrt τ) * (2 * inner ℝ x v) := by
    simp only [_root_.smul_apply, two_smul, _root_.add_apply, smul_eq_mul, innerSL_apply_apply]
    ring
  rw [hv] at hd
  exact (mul_left_cancel₀ hne hd).symm

end PoincareConjecture.M10
