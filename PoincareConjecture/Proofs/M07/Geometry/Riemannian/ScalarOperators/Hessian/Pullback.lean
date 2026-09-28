import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter VectorField

namespace PoincareConjecture.LeviCivitaData

universe u v

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}
  {f : M → N} {x : M} {u : N → ℝ}

theorem hessian_comp_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (f x))
    (v w : TangentSpace (𝓡 n) x) :
    D.hessian (u ∘ f) x v w = D'.hessian u (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) := by
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
  rw [D.hessian_eq_inner_connection_gradient (hu.comp x hf),
    D'.hessian_eq_inner_connection_gradient hu, congrArg (fun L ↦ L v) hc,
    D.connection_mpullback_of_metric_pullback D' hf hinv hmetric
      ((D'.contMDiffAt_gradient hu).mdifferentiableAt (by simp)),
    hmetric.self_of_nhds]
  simp only [hinv.self_of_nhds.self_apply_inverse]

theorem abs_hessian_le_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (f x))
    {C : ℝ}
    (hbound : ∀ v w : TangentSpace (𝓡 n) x,
      |D.hessian (u ∘ f) x v w| ≤ C * g.tangentNorm x v * g.tangentNorm x w)
    (v w : TangentSpace (𝓡 n) (f x)) :
    |D'.hessian u (f x) v w| ≤ C * h.tangentNorm (f x) v * h.tangentNorm (f x) w := by
  have hnorm (a : TangentSpace (𝓡 n) (f x)) :
      g.tangentNorm x ((mfderiv (𝓡 n) (𝓡 n) f x).inverse a) =
        h.tangentNorm (f x) a := by
    unfold RiemannianMetric.tangentNorm
    rw [hmetric.self_of_nhds]
    simp only [hinv.self_of_nhds.self_apply_inverse]
  have hb := hbound ((mfderiv (𝓡 n) (𝓡 n) f x).inverse v)
    ((mfderiv (𝓡 n) (𝓡 n) f x).inverse w)
  rw [D.hessian_comp_of_metric_pullback D' hf hinv hmetric hu] at hb
  simpa only [hinv.self_of_nhds.self_apply_inverse, hnorm] using hb

end PoincareConjecture.LeviCivitaData
