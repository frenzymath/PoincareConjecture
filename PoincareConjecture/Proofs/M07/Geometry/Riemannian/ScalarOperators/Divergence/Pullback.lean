import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

namespace PoincareConjecture.LeviCivitaData

universe u v

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}
  {f : M → N} {x : M} {u : N → ℝ}


theorem gradient_comp_eq_mpullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f x)
    (hu : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) u (f x))
    (hinv : (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible)
    (hmetric : ∀ a b : TangentSpace (𝓡 n) x,
      g.inner x a b = h.inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x a) (mfderiv (𝓡 n) (𝓡 n) f x b)) :
    D.gradient (u ∘ f) x = mpullback (𝓡 n) (𝓡 n) f (D'.gradient u) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  change g.inner x (D.gradient (u ∘ f) x) w = g.inner x _ w
  rw [D.inner_gradient, mvfderiv_comp x hu hf, hmetric]
  simp only [ContinuousLinearMap.comp_apply, mpullback, hinv.self_apply_inverse,
    D'.inner_gradient]


theorem laplacian_comp_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (f x)) :
    D.laplacian (u ∘ f) x = D'.laplacian u (f x) := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  have hf1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞))
  have hu1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hu.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞))
  have hgrad : D.gradient (u ∘ f) =ᶠ[𝓝 x]
      mpullback (𝓡 n) (𝓡 n) f (D'.gradient u) := by
    filter_upwards [hf1, hf.continuousAt.eventually hu1, hinv, hmetric]
      with y hfy huy hiy hmy
    exact D.gradient_comp_eq_mpullback D' (hfy.mdifferentiableAt (by simp))
      (huy.mdifferentiableAt (by simp)) hiy hmy
  have hsource := (D.contMDiffAt_gradient (hu.comp x hf)).mdifferentiableAt (by simp)
  have hpull : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (mpullback (𝓡 n) (𝓡 n) f (D'.gradient u))) x := by
    apply hsource.congr_of_eventuallyEq
    filter_upwards [hgrad] with y hy
    simp only [← hy]
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hsource hpull (by simp) hgrad
  have htransport : (D.connection (D.gradient (u ∘ f)) x).toLinearMap =
      (mfderiv (𝓡 n) (𝓡 n) f x).inverse.toLinearMap.comp
        ((D'.connection (D'.gradient u) (f x)).toLinearMap.comp
          (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap) := by
    ext v
    change D.connection (D.gradient (u ∘ f)) x v = _
    rw [congrArg (fun L => L v) hc]
    exact D.connection_mpullback_of_metric_pullback D' hf hinv hmetric
      ((D'.contMDiffAt_gradient hu).mdifferentiableAt (by simp)) v
  rw [D.laplacian_eq_trace_connection_gradient (hu.comp x hf),
    D'.laplacian_eq_trace_connection_gradient hu, htransport,
    LinearMap.trace_comp_comm']
  congr 1
  ext v
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    hinv.self_of_nhds.self_apply_inverse]

end PoincareConjecture.LeviCivitaData
