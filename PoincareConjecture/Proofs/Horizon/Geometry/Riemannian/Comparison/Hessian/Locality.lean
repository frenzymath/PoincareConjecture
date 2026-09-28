import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hessian_mul_at (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y * h y) x u v =
      f x * D.hessian h x u v + h x * D.hessian f x u v +
      mvfderiv (𝓡 n) f x u * mvfderiv (𝓡 n) h x v +
      mvfderiv (𝓡 n) h x u * mvfderiv (𝓡 n) f x v := by
  have hfx := hf.mdifferentiableAt (by simp)
  have hhx := hh.mdifferentiableAt (by simp)
  have hgf := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have hgh := (D.contMDiffAt_gradient hh).mdifferentiableAt (by simp)
  have hfh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f y * h y) x := hf.smul hh
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  have hhn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hh.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  have heq : D.gradient (fun y => f y * h y) =ᶠ[𝓝 x]
      f • D.gradient h + h • D.gradient f := by
    filter_upwards [hfn, hhn] with y hfy hhy
    exact D.gradient_mul (hfy.mdifferentiableAt (by simp))
      (hhy.mdifferentiableAt (by simp))
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((D.contMDiffAt_gradient hfh).mdifferentiableAt (by simp))
    (mdifferentiableAt_add_section (hfx.smul_section hgh) (hhx.smul_section hgf))
    (by simp) heq
  rw [D.hessian_eq_inner_connection_gradient hfh,
    D.hessian_eq_inner_connection_gradient hf,
    D.hessian_eq_inner_connection_gradient hh, congrArg (fun L => L u) hc,
    D.connection.isCovariantDerivativeOn.add (hfx.smul_section hgh)
      (hhx.smul_section hgf),
    D.connection.isCovariantDerivativeOn.leibniz hgh hfx,
    D.connection.isCovariantDerivativeOn.leibniz hgf hhx]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul, D.inner_gradient]
  ring

theorem hessian_const_add_at (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (c : ℝ)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => c + f y) x u v = D.hessian f x u v := by
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞))
  have hd : ∀ᶠ y in 𝓝 x,
      mvfderiv (𝓡 n) (fun z => c + f z) y = mvfderiv (𝓡 n) f y := by
    filter_upwards [hnear] with y hy
    rw [mvfderiv_fun_add mdifferentiableAt_const (hy.mdifferentiableAt (by simp)),
      mvfderiv_const, zero_add]
  unfold hessian hessianOnFields
  have heq : (fun y => mvfderiv (𝓡 n) (fun z => c + f z) y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) =ᶠ[𝓝 x]
      (fun y => mvfderiv (𝓡 n) f y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) := by
    filter_upwards [hd] with y hy
    rw [hy]
  rw [Poincare.mvfderiv_eq_of_eventuallyEq heq, hd.self_of_nhds]

end PoincareConjecture.LeviCivitaData
