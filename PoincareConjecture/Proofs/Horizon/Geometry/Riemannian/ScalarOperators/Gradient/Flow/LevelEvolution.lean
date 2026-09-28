import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Expansion
import Mathlib.Analysis.Calculus.MeanValue







set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology
set_option backward.isDefEq.respectTransparency false
namespace PoincareConjecture.LeviCivitaData

theorem comp_normalizedGradient_eq_add_on
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hIcon : IsPreconnected I)
    (hf : ∀ t ∈ I, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ t))
    (hreg : ∀ t ∈ I, g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t)) ≠ 0)
    (hγ : IsMIntegralCurveOn (I := 𝓡 n) γ (D.normalizedGradient f) I)
    {a t : ℝ} (ha : a ∈ I) (ht : t ∈ I) :
    f (γ t) = f (γ a) + (t - a) := by
  have hd (s : ℝ) (hs : s ∈ I) : HasDerivAt (fun t => f (γ t)) 1 s := by
    have hcurve := (hγ.isMIntegralCurveAt (hI.mem_nhds hs)).hasMFDerivAt
    have hcomp := (hf s hs).hasMFDerivAt.comp s hcurve
    have hd' := (hasMFDerivAt_iff_hasFDerivAt.mp hcomp).hasDerivAt
    change HasDerivAt (fun t => f (γ t))
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ s) ((1 : ℝ) • D.normalizedGradient f (γ s))) s at hd'
    have he : mvfderiv (𝓡 n) f (γ s) (D.normalizedGradient f (γ s)) = 1 := by
      simp only [normalizedGradient, map_smul, smul_eq_mul, ← D.inner_gradient]
      exact inv_mul_cancel₀ (hreg s hs)
    convert hd' using 1
    simpa [mvfderiv, NormedSpace.fromTangentSpace] using he.symm
  have hr (s : ℝ) : HasDerivAt (fun t => f (γ a) + (t - a)) 1 s := by
    simpa using ((hasDerivAt_id s).sub_const a).const_add (f (γ a))
  exact hI.eqOn_of_deriv_eq hIcon
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s _ => (hr s).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv.trans (hr s).deriv.symm) ha (by simp) ht
end PoincareConjecture.LeviCivitaData
