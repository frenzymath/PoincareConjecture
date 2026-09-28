import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.VectorField.Commutator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma hessian_eq_mvfderiv_on_field (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    {Z : (y : M) → TangentSpace (𝓡 n) y}
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) (a : TangentSpace (𝓡 n) x) :
    D.hessian f x a (Z x) =
      mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (Z y)) x a -
        mvfderiv (𝓡 n) f x (D.connection Z x a) := by
  rw [D.hessian_eq_inner_connection_gradient hf]
  have h := D.hessianOnFields_eq_inner_connection_gradient hf
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) hZ
  simpa only [hessianOnFields, FiberBundle.extend_apply_self] using h.symm

theorem covariantTensorDerivative_hessian_commutator (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x ![a, b, c] -
      D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x ![b, a, c] =
        -mvfderiv (𝓡 n) f x (D.curvature x a b c) := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) c
  have hX := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) a
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) b
  have hZ := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) c
  have hZf := contMDiffAt_mvfderiv_apply (hf x) hZ
  have hexpand (a b : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x ![a, b, c] =
        mvfderiv (𝓡 n)
          (fun y => mvfderiv (𝓡 n) (fun z => mvfderiv (𝓡 n) f z (Z z)) y
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b y)) x a -
        mvfderiv (𝓡 n)
          (fun y => mvfderiv (𝓡 n) f y
            (D.connection Z y (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b y))) x a -
        (mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (Z y)) x
            (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b) x a) -
          mvfderiv (𝓡 n) f x
            (D.connection Z x
              (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b) x a))) -
        (mvfderiv (𝓡 n)
            (fun y => mvfderiv (𝓡 n) f y
              (D.connection Z y (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a y))) x b -
          mvfderiv (𝓡 n) f x
            (D.connection (D.covariantDerivativeOnFields
              (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) Z) x b)) := by
    let A := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    let B := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
    have hA := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) a
    have hB := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) b
    have hAZ := D.contMDiffAt_covariantDerivativeOnFields hA hZ
    have hBZ := D.contMDiffAt_covariantDerivativeOnFields hB hZ
    have heq : (fun y => D.hessian f y (B y) (Z y)) =ᶠ[𝓝 x]
        (fun y => mvfderiv (𝓡 n) (fun z => mvfderiv (𝓡 n) f z (Z z)) y (B y) -
          mvfderiv (𝓡 n) f y (D.connection Z y (B y))) := by
      filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hZ] with y hy
      exact D.hessian_eq_mvfderiv_on_field (hf y) hy (B y)
    have hd : mvfderiv (𝓡 n) (fun y => D.hessian f y (B y) (Z y)) x =
        mvfderiv (𝓡 n)
          (fun y => mvfderiv (𝓡 n) (fun z => mvfderiv (𝓡 n) f z (Z z)) y (B y) -
            mvfderiv (𝓡 n) f y (D.connection Z y (B y))) x := by
      unfold mvfderiv
      rw [heq.mfderiv_eq]
      congr 2
    simp only [covariantTensorDerivative, Fin.sum_univ_two, Matrix.cons_val_zero]
    change mvfderiv (𝓡 n) (fun y => D.hessian f y (B y) (Z y)) x a -
      (D.hessian f x (D.connection B x a) c +
        D.hessian f x b (D.connection Z x a)) = _
    rw [hd]
    have hsub := mvfderiv_fun_sub
      ((contMDiffAt_mvfderiv_apply hZf hB).mdifferentiableAt (by simp))
      ((contMDiffAt_mvfderiv_apply (hf x) hBZ).mdifferentiableAt (by simp))
    simp only [covariantDerivativeOnFields] at hsub
    rw [hsub]
    have hfirst := D.hessian_eq_mvfderiv_on_field (hf x)
      (hZ.mdifferentiableAt (by simp)) (D.connection B x a)
    have hsecond := D.hessian_eq_mvfderiv_on_field (hf x)
      (hAZ.mdifferentiableAt (by simp)) b
    simp only [covariantDerivativeOnFields, FiberBundle.extend_apply_self] at hfirst hsecond
    rw [hfirst, hsecond]
    simp only [sub_apply, B]
    ring
  rw [hexpand a b, hexpand b a]
  have hcomm := Poincare.Manifold.VectorField.mfderiv_mlieBracket_eq_commutator_of_contMDiffAt
    X Y x hZf (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
  have htors := D.covariantDerivativeOnFields_sub_swap
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
  simp only [covariantDerivativeOnFields, FiberBundle.extend_apply_self] at htors
  simp only [X, Y, FiberBundle.extend_apply_self] at hcomm
  rw [← htors, map_sub] at hcomm
  simp only [curvature, curvatureOnFields, FiberBundle.extend_apply_self]
  rw [← htors]
  simp only [map_sub, Z]
  unfold covariantDerivativeOnFields
  linarith only [hcomm]

end PoincareConjecture.LeviCivitaData
