import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff.Support
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]



lemma hasCompactSupport_radial_cutoff (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) (p : M) {R : ℝ} (hR : 0 < R)
    {χ : ℝ → ℝ} (hzero : ∀ r, 2 ≤ r → χ r = 0) :
    HasCompactSupport (fun x => χ ((g.edist p x).toReal / R)) := by
  have hball : {x | (g.edist p x).toReal ≤ 2 * R} =
      {x | g.edist p x ≤ ENNReal.ofReal (2 * R)} := by
    ext x
    exact (ENNReal.le_ofReal_iff_toReal_le (g.edist_ne_top p x) (by positivity)).symm
  apply HasCompactSupport.intro'
    (K := {x | (g.edist p x).toReal ≤ 2 * R})
    (by rw [hball]; exact g.isCompact_closedBall_of_metricComplete hcomplete p (2 * R))
    (isClosed_le (g.continuous_toReal_edist p) continuous_const)
  intro x hx
  apply hzero
  exact (le_div_iff₀ hR).mpr (le_of_lt (lt_of_not_ge hx))



lemma radial_cutoff_lower_supports_of_distance_supports
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    (hone : ∀ r, r ≤ 1 → χ r = 1)
    {A B C m k R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hm : 0 ≤ m) (hk : 0 ≤ k) (hR : 0 < R)
    (hdA : ∀ r, deriv χ r ^ 2 ≤ A * χ r)
    (hdB : ∀ r, -B ≤ deriv (deriv χ) r) (hdC : ∀ r, -C ≤ deriv χ r)
    (hsupport : ∀ x, R ≤ (g.edist p x).toReal →
      ∃ (U : Set M) (ρ : M → ℝ), IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ U ∧ ρ x = (g.edist p x).toReal ∧
        (∀ y ∈ U, (g.edist p y).toReal ≤ ρ y) ∧
        g.inner x (D.gradient ρ x) (D.gradient ρ x) = 1 ∧
        D.laplacian ρ x ≤ 2 * m / (g.edist p x).toReal + m * k)
    (x : M) :
    ∃ (U : Set M) (σ : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U ∧ σ x = χ ((g.edist p x).toReal / R) ∧
      (∀ y ∈ U, σ y ≤ χ ((g.edist p y).toReal / R)) ∧
      g.inner x (D.gradient σ x) (D.gradient σ x) ≤
        (A / R ^ 2) * χ ((g.edist p x).toReal / R) ∧
      -(B / R ^ 2 + C * (2 * m / R + m * k) / R) ≤ D.laplacian σ x := by
  by_cases hx : (g.edist p x).toReal < R
  · let U := {y | (g.edist p y).toReal < R}
    have he (y : M) (hy : y ∈ U) : χ ((g.edist p y).toReal / R) = 1 :=
      hone _ ((div_le_one hR).mpr hy.le)
    refine ⟨U, fun _ => 1, isOpen_lt (g.continuous_toReal_edist p) continuous_const,
      hx, contMDiffOn_const, (he x hx).symm, fun y hy => (he y hy).ge, ?_, ?_⟩
    · simp only [LeviCivitaData.gradient, mvfderiv_const, map_zero, he x hx]
      positivity
    · simp only [LeviCivitaData.laplacian, LeviCivitaData.hessian,
        LeviCivitaData.hessianOnFields, mvfderiv_const, zero_apply, sub_self,
        Finset.sum_const_zero]
      exact neg_nonpos.mpr (by positivity)
  · obtain ⟨U, ρ, hU, hxU, hρ, heq, hle, hg, hl⟩ := hsupport x (le_of_not_gt hx)
    apply D.radial_cutoff_lower_support hχ hanti hR (by positivity) hdA hdB hdC
      hU hxU hρ heq hle hg
    apply hl.trans
    have h : 2 * m / (g.edist p x).toReal ≤ 2 * m / R :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hm) hR (le_of_not_gt hx)
    linarith

end PoincareConjecture.RiemannianMetric
