import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle
open Bundle Set

namespace PoincareConjecture.RiemannianMetric

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem exists_local_gradientIntegralCurveAt
    {D : LeviCivitaData g} {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveAt γ (D.gradient f) 0 := by
  apply exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (I := 𝓡 n) 0
  exact (D.contMDiffAt_gradient (hf x)).of_le (by simp)

theorem hasDerivAt_comp_integralCurve
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hγ : IsMIntegralCurve γ (D.gradient f)) (t : ℝ) :
    HasDerivAt (f ∘ γ)
      (mvfderiv (𝓡 n) f (γ t) (D.gradient f (γ t))) t := by
  have hFd : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ t)
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ t)) :=
    ((hf (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := hFd.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply hcomp.congr_mfderiv
  ext
  exact (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ t))
    (one_smul ℝ (D.gradient f (γ t)))).trans (one_smul ℝ _).symm

theorem hasDerivAt_comp_integralCurve_eq_one
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f)
    (hγ : IsMIntegralCurve γ (D.gradient f)) (t : ℝ) :
    HasDerivAt (f ∘ γ) 1 t := by
  have h := hasDerivAt_comp_integralCurve hf hγ t
  have hu := hunit (γ t)
  rw [D.inner_gradient] at hu
  simpa [hu] using h

theorem deriv_comp_integralCurve_eq_one
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f)
    (hγ : IsMIntegralCurve γ (D.gradient f)) :
    ∀ t, deriv (f ∘ γ) t = 1 := by
  intro t
  exact (hasDerivAt_comp_integralCurve_eq_one hf hunit hγ t).deriv

theorem comp_integralCurve_eq_add
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f)
    (hγ : IsMIntegralCurve γ (D.gradient f)) (t : ℝ) :
    f (γ t) = f (γ 0) + t := by
  let φ : ℝ → ℝ := fun s => f (γ s)
  let ψ : ℝ → ℝ := fun s => f (γ 0) + s
  have hφ : DifferentiableOn ℝ φ (Set.univ : Set ℝ) := by
    intro s hs
    exact (hasDerivAt_comp_integralCurve_eq_one hf hunit hγ s).differentiableAt
      |>.differentiableWithinAt
  have hψ : DifferentiableOn ℝ ψ (Set.univ : Set ℝ) := by
    exact (differentiableOn_const (s := (Set.univ : Set ℝ)) (f (γ 0))).add
      differentiableOn_id
  have hderiv : (Set.univ : Set ℝ).EqOn (deriv φ) (deriv ψ) := by
    intro s hs
    change deriv (f ∘ γ) s = deriv ψ s
    rw [deriv_comp_integralCurve_eq_one hf hunit hγ s]
    simp [ψ]
  have heq := IsOpen.eqOn_of_deriv_eq isOpen_univ
    (PreconnectedSpace.isPreconnected_univ : IsPreconnected (Set.univ : Set ℝ))
    hφ hψ hderiv (show (0 : ℝ) ∈ Set.univ by simp)
    (by simp [φ, ψ])
  simpa [φ, ψ] using heq (Set.mem_univ t)

theorem integralCurve_value_eq_add
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f)
    (hγ : IsMIntegralCurve γ (D.gradient f))
    {x : M} (hγ0 : γ 0 = x) (t : ℝ) :
    f (γ t) = f x + t := by
  rw [comp_integralCurve_eq_add hf hunit hγ t, hγ0]

theorem integralCurve_hits_zero
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f)
    (hγ : IsMIntegralCurve γ (D.gradient f))
    {x : M} (hγ0 : γ 0 = x) :
    f (γ (-f x)) = 0 := by
  rw [integralCurve_value_eq_add hf hunit hγ hγ0]
  ring

theorem integralCurve_zero_time_unique
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient D f)
    (hγ : IsMIntegralCurve γ (D.gradient f))
    {x : M} (hγ0 : γ 0 = x) {s : ℝ} (hs : f (γ s) = 0) :
    s = -f x := by
  have h := integralCurve_value_eq_add hf hunit hγ hγ0 s
  rw [hs] at h
  linarith

end PoincareConjecture.RiemannianMetric
