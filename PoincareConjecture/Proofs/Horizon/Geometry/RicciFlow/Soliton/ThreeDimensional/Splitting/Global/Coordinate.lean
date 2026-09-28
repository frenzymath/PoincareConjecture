import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.LocalParallel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiffAt_nullCoordinate (D : LeviCivitaData g)
    {f : M → ℝ} {V : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => 2 * g.inner y (D.gradient f y) (V y)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact contMDiffAt_const.mul ((D.contMDiffAt_gradient hf).inner_bundle hV)

theorem mvfderiv_nullCoordinate (D : LeviCivitaData g)
    {f : M → ℝ} {V : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hparallel : ∀ v, D.connection V x v = 0)
    (hsol : ∀ v, D.hessian f x v (V x) = (1 / 2 : ℝ) * g.inner x v (V x))
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => 2 * g.inner y (D.gradient f y) (V y)) x v =
      g.inner x (V x) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := D.metricCompatible.mvfderiv_inner_eq
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    ((D.contMDiffAt_gradient hf).mdifferentiableAt (by simp))
    (hV.mdifferentiableAt (by simp))
  change mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (V y)) x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x) =
    g.inner x (D.connection (D.gradient f) x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) (V x) +
    g.inner x (D.gradient f x) (D.connection V x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) at h
  simp only [FiberBundle.extend_apply_self, hparallel, map_zero, add_zero] at h
  rw [← D.hessian_eq_inner_connection_gradient hf, hsol] at h
  rw [mvfderiv_const_mul]
  change 2 * mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (V y)) x v = _
  rw [h, g.symm x v (V x)]
  ring

theorem gradient_nullCoordinate (D : LeviCivitaData g)
    {f : M → ℝ} {V : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hparallel : ∀ v, D.connection V x v = 0)
    (hsol : ∀ v, D.hessian f x v (V x) = (1 / 2 : ℝ) * g.inner x v (V x)) :
    D.gradient (fun y => 2 * g.inner y (D.gradient f y) (V y)) x = V x := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [D.inner_gradient]
  exact mvfderiv_nullCoordinate D hf hV hparallel hsol v

theorem hessian_nullCoordinate (D : LeviCivitaData g)
    {f : M → ℝ} {V : (y : M) → TangentSpace (𝓡 n) y} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U)
    (hparallel : ∀ x ∈ U, ∀ v, D.connection V x v = 0)
    (hsol : ∀ x ∈ U, ∀ v,
      D.hessian f x v (V x) = (1 / 2 : ℝ) * g.inner x v (V x))
    {x : M} (hx : x ∈ U) (v w : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => 2 * g.inner y (D.gradient f y) (V y)) x v w = 0 := by
  have hc := contMDiffAt_nullCoordinate D
    (hf.contMDiffAt (hU.mem_nhds hx)) (hV.contMDiffAt (hU.mem_nhds hx))
  have heq : D.gradient (fun y => 2 * g.inner y (D.gradient f y) (V y)) =ᶠ[𝓝 x] V := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact gradient_nullCoordinate D (hf.contMDiffAt (hU.mem_nhds hy))
      (hV.contMDiffAt (hU.mem_nhds hy)) (hparallel y hy) (hsol y hy)
  have hd := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((D.contMDiffAt_gradient hc).mdifferentiableAt (by simp))
    ((hV.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) (by simp) heq
  rw [D.hessian_eq_inner_connection_gradient hc, congrArg (fun L => L v) hd,
    hparallel x hx v, map_zero, zero_apply]

end PoincareConjecture.RicciFlow.Splitting
