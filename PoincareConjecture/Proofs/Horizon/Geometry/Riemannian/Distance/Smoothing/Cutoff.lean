import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.FiniteCutoffs
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Locality


noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

universe u



def biasedCutoff {M : Type u} (θ ψ f : M → ℝ) (Q a : ℝ) : M → ℝ :=
  fun x => θ x * f x + (1 - θ x) * Q + a * (1 - ψ x)

section Topological

variable {M : Type u} [TopologicalSpace M]

theorem mem_of_inner_cutoff_ne_zero {U : Set M} {θ ψ : M → ℝ}
    (hθU : tsupport θ ⊆ U)
    (hθone : ∀ y ∈ tsupport ψ, θ =ᶠ[𝓝 y] 1)
    {x : M} (hx : ψ x ≠ 0) : x ∈ U := by
  have hθx : θ x = 1 := (hθone x (subset_tsupport ψ hx)).self_of_nhds
  exact hθU (subset_tsupport θ (by simp [hθx]))

theorem cutoff_extension_eventuallyEq_of_inner_ne_zero
    {θ ψ f : M → ℝ} {Q : ℝ}
    (hθone : ∀ y ∈ tsupport ψ, θ =ᶠ[𝓝 y] 1)
    {x : M} (hx : ψ x ≠ 0) :
    (fun y => θ y * f y + (1 - θ y) * Q) =ᶠ[𝓝 x] f := by
  filter_upwards [hθone x (subset_tsupport ψ hx)] with y hy
  change θ y = 1 at hy
  simp [hy]

theorem biasedCutoff_eventuallyEq_of_ne_zero {θ ψ f : M → ℝ} {Q a : ℝ}
    (hθone : ∀ y ∈ tsupport ψ, θ =ᶠ[𝓝 y] 1)
    {x : M} (hx : ψ x ≠ 0) :
    biasedCutoff θ ψ f Q a =ᶠ[𝓝 x] (fun y => f y + a * (1 - ψ y)) := by
  filter_upwards [cutoff_extension_eventuallyEq_of_inner_ne_zero
    (f := f) (Q := Q) hθone hx] with y hy
  exact congrArg (fun z => z + a * (1 - ψ y)) hy


theorem cutoff_extension_lower_bound {θ f d : M → ℝ} {U : Set M} {Q ξ : ℝ}
    (hθbounds : ∀ y, 0 ≤ θ y ∧ θ y ≤ 1) (hθU : tsupport θ ⊆ U)
    (hξ : 0 ≤ ξ) (happrox : ∀ y ∈ U, |f y - d y| ≤ ξ)
    {x : M} (hQ : d x ≤ Q) :
    d x - ξ ≤ θ x * f x + (1 - θ x) * Q := by
  by_cases hx : θ x = 0
  · simp only [hx, zero_mul, sub_zero, one_mul, zero_add]
    linarith
  · have hf := (abs_le.mp (happrox x (hθU (subset_tsupport θ hx)))).1
    have hθ := hθbounds x
    have hf' := mul_le_mul_of_nonneg_left (show d x - ξ ≤ f x by linarith) hθ.1
    have hQ' := mul_le_mul_of_nonneg_left
      (show d x - ξ ≤ Q by linarith) (show 0 ≤ 1 - θ x by linarith)
    nlinarith


theorem biasedCutoff_lower_bound {θ ψ f d : M → ℝ} {U : Set M} {Q a ξ : ℝ}
    (hθbounds : ∀ y, 0 ≤ θ y ∧ θ y ≤ 1) (hθU : tsupport θ ⊆ U)
    (hξ : 0 ≤ ξ) (happrox : ∀ y ∈ U, |f y - d y| ≤ ξ)
    {x : M} (hQ : d x ≤ Q) :
    d x - ξ + a * (1 - ψ x) ≤ biasedCutoff θ ψ f Q a x :=
  add_le_add (cutoff_extension_lower_bound hθbounds hθU hξ happrox hQ) le_rfl

theorem biasedCutoff_le_of_inner_eq_one {θ ψ f d : M → ℝ} {U : Set M}
    {Q a ξ : ℝ} (hθU : tsupport θ ⊆ U)
    (hθone : ∀ y ∈ tsupport ψ, θ =ᶠ[𝓝 y] 1)
    (happrox : ∀ y ∈ U, |f y - d y| ≤ ξ) {x : M} (hx : ψ x = 1) :
    biasedCutoff θ ψ f Q a x ≤ d x + ξ := by
  have hxne : ψ x ≠ 0 := by simp [hx]
  have hxU := mem_of_inner_cutoff_ne_zero hθU hθone hxne
  have heq := (biasedCutoff_eventuallyEq_of_ne_zero
    (f := f) (Q := Q) (a := a) hθone hxne).self_of_nhds
  have hf := (abs_le.mp (happrox x hxU)).2
  simp only [hx, sub_self, mul_zero, add_zero] at heq
  linarith

end Topological

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem contMDiff_biasedCutoff {U : Set M} (hU : IsOpen U)
    {θ ψ f : M → ℝ} (hθ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ θ)
    (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) (hθU : tsupport θ ⊆ U)
    (Q a : ℝ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (biasedCutoff θ ψ f Q a) :=
  (contMDiff_cutoff_extension hU hθ hf hθU Q).add
    (contMDiff_const.mul (contMDiff_const.sub hψ))

namespace LeviCivitaData

variable [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}



theorem biasedCutoff_derivative_bounds_at (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {θ ψ f : M → ℝ}
    (hθ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ θ)
    (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hθU : tsupport θ ⊆ U)
    (hθone : ∀ y ∈ tsupport ψ, θ =ᶠ[𝓝 y] 1)
    {Q a L H P B : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L) (hP : 0 ≤ P)
    {x : M} (hgrad : g.tangentNorm x (D.gradient f x) ≤ L)
    (hhess : ∀ v : TangentSpace (𝓡 n) x,
      D.hessian f x v v ≤ H * g.inner x v v)
    (hψfirst : ∀ v : TangentSpace (𝓡 n) x,
      |mvfderiv (𝓡 n) ψ x v| ≤ P * g.tangentNorm x v)
    (hψsecond : ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian ψ x v v| ≤ B * g.inner x v v)
    (hx : ψ x ≠ 0) :
    g.tangentNorm x (D.gradient (biasedCutoff θ ψ f Q a) x) ≤ L + a * P ∧
      ∀ v : TangentSpace (𝓡 n) x,
        D.hessian (biasedCutoff θ ψ f Q a) x v v ≤
          (H + a * B) * g.inner x v v := by
  let F : M → ℝ := fun y => θ y * f y + (1 - θ y) * Q
  have hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F :=
    contMDiff_cutoff_extension hU hθ hf hθU Q
  have hFx : F =ᶠ[𝓝 x] f := cutoff_extension_eventuallyEq_of_inner_ne_zero hθone hx
  have hbias : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => a * (1 - ψ y)) :=
    contMDiff_const.mul (contMDiff_const.sub hψ)
  constructor
  · apply (D.gradient_norm_le_iff _ x (add_nonneg hL (mul_nonneg ha hP))).mpr
    intro v
    change |mvfderiv (𝓡 n) (fun y => F y + a * (1 - ψ y)) x v| ≤ _
    rw [mvfderiv_fun_add ((hF x).mdifferentiableAt (by simp))
      ((hbias x).mdifferentiableAt (by simp)),
      add_apply, Poincare.mvfderiv_eq_of_eventuallyEq hFx,
      mvfderiv_const_mul, mvfderiv_fun_sub mdifferentiableAt_const
        ((hψ x).mdifferentiableAt (by simp))]
    simp only [mvfderiv_const, zero_sub, neg_apply, mul_neg, ← sub_eq_add_neg]
    calc
      |mvfderiv (𝓡 n) f x v - a * mvfderiv (𝓡 n) ψ x v| ≤
          |mvfderiv (𝓡 n) f x v| + a * |mvfderiv (𝓡 n) ψ x v| := by
        simpa [abs_mul, abs_of_nonneg ha] using
          abs_sub (mvfderiv (𝓡 n) f x v) (a * mvfderiv (𝓡 n) ψ x v)
      _ ≤ L * g.tangentNorm x v + a * (P * g.tangentNorm x v) :=
        add_le_add ((D.abs_mvfderiv_le_gradient_norm f x v).trans
          (mul_le_mul_of_nonneg_right hgrad (Real.sqrt_nonneg _)))
          (mul_le_mul_of_nonneg_left (hψfirst v) ha)
      _ = (L + a * P) * g.tangentNorm x v := by ring
  · intro v
    have hsub : (fun y => 1 - ψ y) = (fun y => 1 + (-1 : ℝ) * ψ y) := by
      funext y
      ring
    have hψhess : D.hessian (fun y => 1 - ψ y) x v v = -D.hessian ψ x v v := by
      have hneg : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (-1 : ℝ) * ψ y) x :=
        contMDiffAt_const.mul (hψ x)
      rw [hsub, D.hessian_const_add_at hneg, D.hessian_const_mul]
      ring
    change D.hessian (fun y => F y + a * (1 - ψ y)) x v v ≤ _
    rw [D.hessian_add hF hbias, D.hessian_eq_of_eventuallyEq hFx,
      D.hessian_const_mul, hψhess]
    have hψlower := (abs_le.mp (hψsecond v)).1
    have hmul := mul_le_mul_of_nonneg_left
      (show -D.hessian ψ x v v ≤ B * g.inner x v v by linarith) ha
    nlinarith [hhess v]



theorem biasedCutoff_derivative_bounds (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {θ ψ f : M → ℝ}
    (hθ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ θ)
    (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hθU : tsupport θ ⊆ U)
    (hθone : ∀ y ∈ tsupport ψ, θ =ᶠ[𝓝 y] 1)
    {Q a L H P B : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (hgrad : ∀ y ∈ U, g.tangentNorm y (D.gradient f y) ≤ L)
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      D.hessian f y v v ≤ H * g.inner y v v)
    (hψfirst : ∀ y, ∀ v : TangentSpace (𝓡 n) y,
      |mvfderiv (𝓡 n) ψ y v| ≤ P * g.tangentNorm y v)
    (hψsecond : ∀ y, ∀ v : TangentSpace (𝓡 n) y,
      |D.hessian ψ y v v| ≤ B * g.inner y v v)
    {x : M} (hx : ψ x ≠ 0) :
    g.tangentNorm x (D.gradient (biasedCutoff θ ψ f Q a) x) ≤ L + a * P ∧
      ∀ v : TangentSpace (𝓡 n) x,
        D.hessian (biasedCutoff θ ψ f Q a) x v v ≤
          (H + a * B) * g.inner x v v := by
  have hxU := mem_of_inner_cutoff_ne_zero hθU hθone hx
  exact D.biasedCutoff_derivative_bounds_at hU hθ hψ hf hθU hθone ha hL hP
    (hgrad x hxU) (hhess x hxU) (hψfirst x) (hψsecond x) hx

end LeviCivitaData

end PoincareConjecture
