import PoincareConjecture.Proofs.M10.RegularGerms
import PoincareConjecture.Definitions.Ch06.ReducedVolume

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}
  {p q : M} {τ : ℝ}

theorem reducedLength_regular_laplacian_le
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    (F.connection (T - τ)).laplacian (fun x ↦ reducedLength F T p x τ) q ≤
      -deriv (fun s ↦ reducedLength F T p q s) τ +
        ((n : ℝ) / 2 - reducedLength F T p q τ) / τ := by
  have h := (hDifferential.regular_point_formulas p q τ r).2.2.2.1
  rw [(regular_time_eventuallyEq r).deriv_eq, regular_laplacian_eq r,
    r.representative_eq (q, τ) r.center_mem] at h
  simpa only [reducedLengthLaplacian, sub_eq_add_neg, add_comm] using
    (le_sub_iff_add_le').mpr h

theorem reducedLength_regular_weak_integrands
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (r : ReducedLengthRegularPoint F T τmax p q τ) (φ : M → ℝ) :
    let H := -deriv (fun s ↦ reducedLength F T p q s) τ +
      ((n : ℝ) / 2 - reducedLength F T p q τ) / τ
    reducedLengthFirstWeakIntegrand F T p τ φ q =
      φ q * H - reducedLength F T p q τ * (F.connection (T - τ)).laplacian φ q ∧
    reducedLengthSecondWeakIntegrand F T p τ φ q =
      -2 * (φ q * H - reducedLength F T p q τ * (F.connection (T - τ)).laplacian φ q) := by
  have ht := (hDifferential.regular_point_formulas p q τ r).1
  have hg := (hDifferential.regular_point_formulas p q τ r).2.1
  rw [(regular_time_eventuallyEq r).deriv_eq,
    r.representative_eq (q, τ) r.center_mem] at ht
  rw [regular_gradientNormSq_eq r, r.representative_eq (q, τ) r.center_mem] at hg
  dsimp only
  simp only [reducedLengthFirstWeakIntegrand, reducedLengthSecondWeakIntegrand, ht, hg]
  constructor <;> ring

end PoincareConjecture.M10
