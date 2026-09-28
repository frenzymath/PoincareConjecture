import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Proofs.M04.ConnectionScalar
import Mathlib.Analysis.Calculus.ContDiff.Deriv








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def scalarGradientSq (g : RiemannianMetric n M) (q : M → ℝ) (x : M) : ℝ :=
  ∑ i, (mvfderiv (𝓡 n) q x (g.orthonormalBasis x i)) ^ 2

set_option backward.isDefEq.respectTransparency false in
theorem scalarGradientSq_pos_iff (g : RiemannianMetric n M) (q : M → ℝ) (x : M) :
    0 < scalarGradientSq g q x ↔ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q x ≠ 0 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hnn : 0 ≤ scalarGradientSq g q x := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  constructor
  · intro hpos hz
    have he : scalarGradientSq g q x = 0 := by
      simp [scalarGradientSq, mvfderiv, hz]
    exact (ne_of_gt hpos) he
  · intro hne
    by_contra hpos
    have hz : scalarGradientSq g q x = 0 := le_antisymm (le_of_not_gt hpos) hnn
    have hb (i) : mvfderiv (𝓡 n) q x (b i) = 0 := by
      have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦
        sq_nonneg (mvfderiv (𝓡 n) q x (b i)))).mp hz i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp he
    apply hne
    ext a
    change mvfderiv (𝓡 n) q x a = 0
    calc
      _ = mvfderiv (𝓡 n) q x (∑ i, inner ℝ (b i) a • b i) :=
        congrArg (mvfderiv (𝓡 n) q x) (b.sum_repr' a).symm
      _ = 0 := by simp only [map_sum, map_smul, hb, smul_zero, Finset.sum_const_zero]

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem laplacian_comp {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} {q : M → ℝ} {φ : ℝ → ℝ} {x : M}
    (hU : IsOpen U) (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U)
    (hφ : ContDiff ℝ ∞ φ) (hx : x ∈ U) :
    D.laplacian (fun y ↦ φ (q y)) x =
      deriv φ (q x) * D.laplacian q x +
        deriv (deriv φ) (q x) * scalarGradientSq g q x := by
  have hqd {y : M} (hy : y ∈ U) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q y :=
    (hq.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hchain {f : ℝ → ℝ} (hf : Differentiable ℝ f) {y : M} (hy : y ∈ U)
      (a : TangentSpace (𝓡 n) y) :
      mvfderiv (𝓡 n) (fun z ↦ f (q z)) y a =
        deriv f (q y) * mvfderiv (𝓡 n) q y a := by
    change mvfderiv (𝓡 n) (f ∘ q) y a = _
    rw [mvfderiv_comp_apply y (hf (q y)).mdifferentiableAt (hqd hy) a]
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
    exact fderiv_eq_deriv_mul (𝕜 := ℝ)
  have hφd : Differentiable ℝ φ := (contDiff_infty_iff_deriv.mp hφ).1
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ'd : Differentiable ℝ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ').1
  have hH (a b : TangentSpace (𝓡 n) x) :
      D.hessian (fun y ↦ φ (q y)) x a b =
        deriv φ (q x) * D.hessian q x a b +
          deriv (deriv φ) (q x) * mvfderiv (𝓡 n) q x a * mvfderiv (𝓡 n) q x b := by
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
    let Q := fun y ↦ mvfderiv (𝓡 n) q y (Y y)
    have heq : (fun y ↦ mvfderiv (𝓡 n) (fun z ↦ φ (q z)) y (Y y)) =ᶠ[𝓝 x]
        (fun y ↦ deriv φ (q y) * Q y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hchain hφd hy (Y y)
    have hQd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) Q x :=
      (contMDiffAt_directional_derivative (hq.contMDiffAt (hU.mem_nhds hx))
        (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) b)).mdifferentiableAt
          (by simp)
    have hpd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ deriv φ (q y)) x :=
      (hφ'd (q x)).mdifferentiableAt.comp x (hqd hx)
    have hder : mvfderiv (𝓡 n)
        (fun y ↦ mvfderiv (𝓡 n) (fun z ↦ φ (q z)) y (Y y)) x a =
        deriv φ (q x) * mvfderiv (𝓡 n) Q x a +
          deriv (deriv φ) (q x) * mvfderiv (𝓡 n) q x a * mvfderiv (𝓡 n) q x b := by
      have he : mvfderiv (𝓡 n)
          (fun y ↦ mvfderiv (𝓡 n) (fun z ↦ φ (q z)) y (Y y)) x =
          mvfderiv (𝓡 n) (fun y ↦ deriv φ (q y) * Q y) x := heq.mfderiv_eq
      rw [he]
      erw [mvfderiv_fun_mul hpd hQd]
      simp only [add_apply, smul_apply, smul_eq_mul, hchain hφ'd hx,
        Q, Y, FiberBundle.extend_apply_self]
      ring
    change mvfderiv (𝓡 n)
        (fun y ↦ mvfderiv (𝓡 n) (fun z ↦ φ (q z)) y (Y y)) x (X x) -
        mvfderiv (𝓡 n) (fun z ↦ φ (q z)) x (D.connection Y x (X x)) =
      deriv φ (q x) * (mvfderiv (𝓡 n) Q x (X x) -
        mvfderiv (𝓡 n) q x (D.connection Y x (X x))) + _
    simp only [X, FiberBundle.extend_apply_self]
    rw [hder, hchain hφd hx]
    ring
  simp only [LeviCivitaData.laplacian, hH, Finset.sum_add_distrib, ← Finset.mul_sum,
    scalarGradientSq, pow_two, mul_assoc]

end PoincareConjecture.M04

