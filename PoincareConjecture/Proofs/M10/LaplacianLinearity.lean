import PoincareConjecture.Proofs.M10.HessianTensorial
import Mathlib.Geometry.Manifold.Algebra.Monoid

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in

theorem hessian_add_scalar (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 2 f) (hh : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 2 h)
    (q : M) (v w : TangentSpace (𝓡 n) q) :
    D.hessian (fun x ↦ f x + h x) q v w = D.hessian f q v w + D.hessian h q v w := by
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) w
  have heq : (fun x ↦ mvfderiv (𝓡 n) (fun y ↦ f y + h y) x (Y x)) =
      fun x ↦ mvfderiv (𝓡 n) f x (Y x) + mvfderiv (𝓡 n) h x (Y x) := by
    funext x
    rw [mvfderiv_fun_add (hf.mdifferentiable two_ne_zero x) (hh.mdifferentiable two_ne_zero x)]
    rfl
  have hY := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self]
  change mvfderiv (𝓡 n) (fun x ↦ mvfderiv (𝓡 n) (fun y ↦ f y + h y) x (Y x)) q v -
      mvfderiv (𝓡 n) (fun y ↦ f y + h y) q (D.connection Y q v) = _
  rw [heq, mvfderiv_fun_add
    (scalar_field_derivative_mdifferentiableAt hf.contMDiffAt hY)
    (scalar_field_derivative_mdifferentiableAt hh.contMDiffAt hY),
    mvfderiv_fun_add (hf.mdifferentiable two_ne_zero q) (hh.mdifferentiable two_ne_zero q)]
  simp only [_root_.add_apply]
  ring

theorem laplacian_add_scalar (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 2 f) (hh : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 2 h)
    (q : M) :
    D.laplacian (fun x ↦ f x + h x) q = D.laplacian f q + D.laplacian h q := by
  simp only [LeviCivitaData.laplacian, hessian_add_scalar D hf hh, Finset.sum_add_distrib]

theorem laplacian_const_scalar (D : LeviCivitaData g) (c : ℝ) (q : M) :
    D.laplacian (fun _ ↦ c) q = 0 := by
  simp only [LeviCivitaData.laplacian, LeviCivitaData.hessian,
    LeviCivitaData.hessianOnFields, mvfderiv_const, zero_apply,
    sub_zero, Finset.sum_const_zero]

theorem laplacian_finsetSum_scalar {ι : Type*} (D : LeviCivitaData g) (s : Finset ι)
    (f : ι → M → ℝ) (hf : ∀ i ∈ s, ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 2 (f i)) (q : M) :
    D.laplacian (fun x ↦ ∑ i ∈ s, f i x) q = ∑ i ∈ s, D.laplacian (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, laplacian_const_scalar]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [laplacian_add_scalar D (hf i (Finset.mem_insert_self _ _))
      (contMDiff_finsetSum (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

end PoincareConjecture.M10
