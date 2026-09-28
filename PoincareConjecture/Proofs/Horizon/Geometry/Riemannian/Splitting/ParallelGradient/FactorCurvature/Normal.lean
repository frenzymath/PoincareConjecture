import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.LevelSet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Curvature.Tensorial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {f : M → ℝ}

theorem curvature_gradient_eq_zero_of_hasZeroHessian
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hz : HasZeroHessian D f)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.curvature x u v (D.gradient f x) = 0 := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have he := D.curvatureOnFields_eq_curvature e.open_baseSet X Y (D.gradient f)
    (LeviCivitaData.contMDiffOn_extend_baseSet x u)
    (LeviCivitaData.contMDiffOn_extend_baseSet x v)
    (D.contMDiff_gradient hf).contMDiffOn (FiberBundle.mem_baseSet_trivializationAt _ _ x)
  have hzero (Z : (y : M) → TangentSpace (𝓡 n) y) :
      (fun y => D.connection (D.gradient f) y (Z y)) = 0 := by
    funext y
    exact connection_gradient_eq_zero_of_hasZeroHessian hf hz y (Z y)
  have hfield : D.curvatureOnFields X Y (D.gradient f) x = 0 := by
    rw [LeviCivitaData.curvatureOnFields, hzero, hzero,
      connection_gradient_eq_zero_of_hasZeroHessian hf hz]
    simp
  simpa only [X, Y, FiberBundle.extend_apply_self] using he.symm.trans hfield

theorem curvatureTensor_gradient_last_eq_zero
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hz : HasZeroHessian D f)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w (D.gradient f x) = 0 := by
  rw [LeviCivitaData.curvatureTensor, curvature_gradient_eq_zero_of_hasZeroHessian hf hz]
  simp

private theorem curvatureTensor_cyclic (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v z w + D.curvatureTensor x v w z u +
      D.curvatureTensor x w u z v = 0 := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hX := LeviCivitaData.contMDiffOn_extend_baseSet x u
  have hY := LeviCivitaData.contMDiffOn_extend_baseSet x v
  have hZ := LeviCivitaData.contMDiffOn_extend_baseSet x w
  have hx := FiberBundle.mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x
  have hb := D.curvatureOnFields_bianchi e.open_baseSet X Y Z hX hY hZ hx
  rw [D.curvatureOnFields_eq_curvature e.open_baseSet X Y Z hX hY hZ hx,
    D.curvatureOnFields_eq_curvature e.open_baseSet Y Z X hY hZ hX hx,
    D.curvatureOnFields_eq_curvature e.open_baseSet Z X Y hZ hX hY hx] at hb
  have hp := congrArg (fun a => g.inner x a z) hb
  simpa only [X, Y, Z, FiberBundle.extend_apply_self, map_add, add_apply,
    map_zero, zero_apply, LeviCivitaData.curvatureTensor] using hp

theorem curvatureTensor_gradient_first_eq_zero
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hz : HasZeroHessian D f)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x (D.gradient f x) u v w = 0 := by
  let N := D.gradient f x
  have h₁ := curvatureTensor_cyclic (D := D) x N u w v
  have h₂ := curvatureTensor_cyclic (D := D) x N v u w
  have h₃ := curvatureTensor_cyclic (D := D) x N w v u
  simp only [N, curvatureTensor_gradient_last_eq_zero hf hz, add_zero] at h₁ h₂ h₃
  have s₁ := D.curvatureTensor_swap_first x w N v u
  have s₂ := D.curvatureTensor_swap_first x u N w v
  have s₃ := D.curvatureTensor_swap_first x v N u w
  have t₁ := D.curvatureTensor_swap_last x N w v u
  have t₂ := D.curvatureTensor_swap_last x N u w v
  have t₃ := D.curvatureTensor_swap_last x N v u w
  dsimp only [N] at s₁ s₂ s₃ t₁ t₂ t₃
  linarith

theorem curvatureTensor_gradient_slots_eq_zero
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hz : HasZeroHessian D f)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x (D.gradient f x) u v w = 0 ∧
    D.curvatureTensor x u (D.gradient f x) v w = 0 ∧
    D.curvatureTensor x u v (D.gradient f x) w = 0 ∧
    D.curvatureTensor x u v w (D.gradient f x) = 0 := by
  refine ⟨curvatureTensor_gradient_first_eq_zero hf hz x u v w, ?_, ?_,
    curvatureTensor_gradient_last_eq_zero hf hz x u v w⟩
  · rw [D.curvatureTensor_swap_first, curvatureTensor_gradient_first_eq_zero hf hz, neg_zero]
  · rw [D.curvatureTensor_swap_last, curvatureTensor_gradient_last_eq_zero hf hz, neg_zero]

end PoincareConjecture.RiemannianMetric
