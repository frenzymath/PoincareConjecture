import PoincareConjecture.Proofs.M10.RegularGerms
import PoincareConjecture.Definitions.Ch06.ReducedVolume
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p q : M} {τ : ℝ}

theorem reducedVolumeDensity_pos (hτ : 0 < τ) :
    0 < reducedVolumeDensity F T p τ q := by
  delta reducedVolumeDensity
  rw [if_pos hτ]
  exact mul_pos (Real.rpow_pos_of_pos hτ _) (Real.exp_pos _)

theorem reducedVolumeDensity_nonneg : 0 ≤ reducedVolumeDensity F T p τ q := by
  by_cases hτ : 0 < τ
  · exact (reducedVolumeDensity_pos hτ).le
  · delta reducedVolumeDensity
    simp only [if_neg hτ, le_refl]

theorem euclideanReducedVolume_pos (n : ℕ) : 0 < euclideanReducedVolume n :=
  Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _

theorem reducedVolumeDensity_hasDerivAt {d : ℝ} (hτ : 0 < τ)
    (hl : HasDerivAt (fun s ↦ reducedLength F T p q s) d τ) :
    HasDerivAt (fun s ↦ reducedVolumeDensity F T p s q)
      (reducedVolumeDensity F T p τ q * (-(n : ℝ) / (2 * τ) - d)) τ := by
  have hp := Real.hasDerivAt_rpow_const (p := -(n : ℝ) / 2) (Or.inl hτ.ne')
  have h := hp.mul hl.neg.exp
  have heq : (fun s ↦ reducedVolumeDensity F T p s q) =ᶠ[𝓝 τ]
      (fun s ↦ Real.rpow s (-(n : ℝ) / 2) * Real.exp (-reducedLength F T p q s)) := by
    filter_upwards [eventually_gt_nhds hτ] with s hs
    exact if_pos hs
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  delta reducedVolumeDensity
  rw [if_pos hτ, Real.rpow_sub_one hτ.ne']
  simp only [Pi.neg_apply, Real.rpow_eq_pow]
  ring

theorem reducedVolumeDensity_regular_hasDerivAt
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    HasDerivAt (fun s ↦ reducedVolumeDensity F T p s q)
      (reducedVolumeDensity F T p τ q *
        (-(n : ℝ) / (2 * τ) - deriv (fun s ↦ reducedLength F T p q s) τ)) τ :=
  reducedVolumeDensity_hasDerivAt r.tau_pos (reducedLength_hasDerivAt r)

end PoincareConjecture.M10
