import PoincareConjecture.Proofs.M08.VariationAction
import Mathlib.Analysis.Calculus.DerivativeTest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

theorem secondDerivative_nonneg_of_localMin {f : ℝ → ℝ} {x q : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x)
    (hd : HasDerivAt (deriv f) q x) : 0 ≤ q := by
  by_contra hq
  have hneg : q < 0 := lt_of_not_ge hq
  have hmax : IsLocalMax f x := isLocalMax_of_deriv_deriv_neg
    (by rw [hd.deriv]; exact hneg) hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hmin, hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hzero : deriv (deriv f) x = 0 := by
    rw [heq.deriv.deriv_eq]
    simp
  have : q = 0 := hd.deriv.symm.trans hzero
  linarith

theorem mixedTerm_eq_zero_of_quadratic_nonneg {B C : ℝ}
    (h : ∀ c : ℝ, 0 ≤ 2 * c * B + c ^ 2 * C) : B = 0 := by
  have hmin : IsLocalMin (fun c : ℝ ↦ 2 * c * B + c ^ 2 * C) 0 := by
    apply Filter.Eventually.of_forall
    intro c
    simpa only [mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
      using h c
  have hd : HasDerivAt (fun c : ℝ ↦ 2 * c * B + c ^ 2 * C) (2 * B) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const B).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const C) using 1 <;>
      first | rfl | norm_num
  have hz := hmin.hasDerivAt_eq_zero hd
  linarith

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem secondVariation_nonneg {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    {p : BackwardTimePath F T τ₁ τ₂}
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p)
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) {q : ℝ}
    (hd : HasDerivAt (fun u ↦ deriv (variationLLength V.toLVariation) u) q 0) :
    0 ≤ q := by
  have hc := (hasDerivAt_variationLLength_integral hM04 V.toLVariation
    (show (0 : ℝ) ∈ V.toLVariation.parameterDomain from
      ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩)).continuousAt
  exact secondDerivative_nonneg_of_localMin (isLocalMin_variationLLength hmin V) hc hd

end PoincareConjecture.M08
