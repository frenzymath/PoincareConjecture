import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Transport.Normalized

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} (D : LeviCivitaData g) {f : M → ℝ}
  (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
  {γ : ℝ → M} (hγ : IsMIntegralCurve γ (D.boundedNormalizedGradient f))

include hf hγ

theorem hasDerivAt_potential_boundedNormalizedGradient (t : ℝ) :
    HasDerivAt (f ∘ γ)
      (g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t)) /
        normalizedGradientDenominator
          (g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t)))) t := by
  have hcomp := (((hf (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
    (hγ t)).hasFDerivAt.hasDerivAt
  convert! hcomp using 1
  change _ = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ t)
    ((1 : ℝ) • D.boundedNormalizedGradient f (γ t))
  rw [one_smul, boundedNormalizedGradient, map_smul]
  change _ = _ * mvfderiv (𝓡 n) f (γ t) (D.gradient f (γ t))
  rw [← D.inner_gradient]
  ring

theorem potential_boundedNormalizedGradient_deriv_bounds (t : ℝ) :
    0 ≤ deriv (f ∘ γ) t ∧ deriv (f ∘ γ) t ≤ 1 := by
  rw [(D.hasDerivAt_potential_boundedNormalizedGradient hf hγ t).deriv]
  let q := g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t))
  have hq : 0 ≤ q := by
    by_cases hz : D.gradient f (γ t) = 0
    · simp [q, hz]
    · exact (g.pos _ _ hz).le
  have hd : 0 < normalizedGradientDenominator q :=
    lt_of_lt_of_le (by norm_num) (normalizedGradientDenominator_lower q)
  exact ⟨div_nonneg hq hd.le,
    (div_le_one hd).mpr (normalizedGradientDenominator_ge q)⟩

theorem potential_boundedNormalizedGradient_monotone :
    Monotone (f ∘ γ) ∧ Antitone (fun t => f (γ t) - t) := by
  have hd := D.hasDerivAt_potential_boundedNormalizedGradient hf hγ
  refine ⟨monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
    (fun t => (D.potential_boundedNormalizedGradient_deriv_bounds hf hγ t).1), ?_⟩
  apply antitone_of_deriv_nonpos
    (fun t => ((hd t).sub (hasDerivAt_id t)).differentiableAt)
  intro t
  rw [((hd t).sub (hasDerivAt_id t)).deriv]
  have h := (D.potential_boundedNormalizedGradient_deriv_bounds hf hγ t).2
  rw [(hd t).deriv] at h
  linarith

theorem potential_boundedNormalizedGradient_eq_add {a : ℝ}
    (ha : ∀ x, a < f x → 1 ≤ g.inner x (D.gradient f x) (D.gradient f x))
    (hstart : a < f (γ 0)) {t : ℝ} (ht : a < f (γ 0) + t) :
    f (γ t) = f (γ 0) + t := by
  obtain ⟨hmono, hanti⟩ := D.potential_boundedNormalizedGradient_monotone hf hγ
  have hhigh (r : ℝ) (hr : r ∈ Ioi (a - f (γ 0))) : a < f (γ r) := by
    by_cases hr0 : 0 ≤ r
    · exact hstart.trans_le (hmono hr0)
    · have h := hanti (le_of_not_ge hr0)
      dsimp only at h
      change a - f (γ 0) < r at hr
      linarith
  have hd (r : ℝ) (hr : r ∈ Ioi (a - f (γ 0))) :
      HasDerivAt (fun s => f (γ s) - s) 0 r := by
    have h := D.hasDerivAt_potential_boundedNormalizedGradient hf hγ r
    have hq := ha (γ r) (hhigh r hr)
    rw [normalizedGradientDenominator_eq hq, div_self (by linarith :
      g.inner (γ r) (D.gradient f (γ r)) (D.gradient f (γ r)) ≠ 0)] at h
    convert! h.sub (hasDerivAt_id r) using 1 <;> simp
  have heq := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv)
    (show t ∈ Ioi (a - f (γ 0)) by change a - f (γ 0) < t; linarith)
    (show (0 : ℝ) ∈ Ioi (a - f (γ 0)) by change a - f (γ 0) < 0; linarith)
  linarith

end PoincareConjecture.LeviCivitaData
