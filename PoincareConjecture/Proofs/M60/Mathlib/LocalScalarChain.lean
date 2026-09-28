import PoincareConjecture.Proofs.M04.ScalarChainRule










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set Filter

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}




theorem laplacian_comp_of_contDiffOn (D : LeviCivitaData g)
    {q : M → ℝ} {φ : ℝ → ℝ} {V : Set ℝ} {x : M}
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q)
    (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ V) (hx : q x ∈ V) :
    D.laplacian (fun y => φ (q y)) x =
      deriv φ (q x) * D.laplacian q x +
        deriv (deriv φ) (q x) * M04.scalarGradientSq g q x := by
  have hqd (y : M) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q y :=
    (hq y).mdifferentiableAt (by simp)
  have hchain {f : ℝ → ℝ} {y : M} (hf : DifferentiableAt ℝ f (q y))
      (a : TangentSpace (𝓡 n) y) :
      mvfderiv (𝓡 n) (fun z => f (q z)) y a =
        deriv f (q y) * mvfderiv (𝓡 n) q y a := by
    change mvfderiv (𝓡 n) (f ∘ q) y a = _
    rw [mvfderiv_comp_apply y hf.mdifferentiableAt (hqd y) a]
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
    exact fderiv_eq_deriv_mul (𝕜 := ℝ)
  have hφ' : ContDiffOn ℝ ∞ (deriv φ) V :=
    hφ.deriv_of_isOpen hV (by simp)
  have hφd {y : M} (hy : q y ∈ V) : DifferentiableAt ℝ φ (q y) :=
    (hφ.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
  have hφ'd {y : M} (hy : q y ∈ V) : DifferentiableAt ℝ (deriv φ) (q y) :=
    (hφ'.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
  have hH (a b : TangentSpace (𝓡 n) x) :
      D.hessian (fun y => φ (q y)) x a b =
        deriv φ (q x) * D.hessian q x a b +
          deriv (deriv φ) (q x) * mvfderiv (𝓡 n) q x a * mvfderiv (𝓡 n) q x b := by
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
    let Q := fun y => mvfderiv (𝓡 n) q y (Y y)
    have heq : (fun y => mvfderiv (𝓡 n) (fun z => φ (q z)) y (Y y)) =ᶠ[𝓝 x]
        (fun y => deriv φ (q y) * Q y) := by
      filter_upwards [hq.continuous.continuousAt.preimage_mem_nhds
        (hV.mem_nhds hx)] with y hy
      exact hchain (hφd hy) (Y y)
    have hQd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) Q x :=
      (M04.contMDiffAt_directional_derivative (hq x)
        (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) b)).mdifferentiableAt (by simp)
    have hpd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => deriv φ (q y)) x :=
      (hφ'd hx).mdifferentiableAt.comp x (hqd x)
    have hder : mvfderiv (𝓡 n)
        (fun y => mvfderiv (𝓡 n) (fun z => φ (q z)) y (Y y)) x a =
        deriv φ (q x) * mvfderiv (𝓡 n) Q x a +
          deriv (deriv φ) (q x) * mvfderiv (𝓡 n) q x a * mvfderiv (𝓡 n) q x b := by
      have he : mvfderiv (𝓡 n)
          (fun y => mvfderiv (𝓡 n) (fun z => φ (q z)) y (Y y)) x =
          mvfderiv (𝓡 n) (fun y => deriv φ (q y) * Q y) x := heq.mfderiv_eq
      rw [he]
      erw [mvfderiv_fun_mul hpd hQd]
      simp only [add_apply, smul_apply, smul_eq_mul, hchain (hφ'd hx),
        Q, Y, FiberBundle.extend_apply_self]
      ring
    change mvfderiv (𝓡 n)
        (fun y => mvfderiv (𝓡 n) (fun z => φ (q z)) y (Y y)) x (X x) -
        mvfderiv (𝓡 n) (fun z => φ (q z)) x (D.connection Y x (X x)) =
      deriv φ (q x) * (mvfderiv (𝓡 n) Q x (X x) -
        mvfderiv (𝓡 n) q x (D.connection Y x (X x))) + _
    simp only [X, FiberBundle.extend_apply_self]
    rw [hder, hchain (hφd hx)]
    ring
  simp only [LeviCivitaData.laplacian, hH, Finset.sum_add_distrib, ← Finset.mul_sum,
    M04.scalarGradientSq, pow_two, mul_assoc]

end PoincareConjecture.M60
