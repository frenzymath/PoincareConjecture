import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CoefficientDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure X)

def schwartzMultiplierLinear : 𝓢(X, ℝ) →ₗ[ℝ] L2 →L[ℝ] L2 where
  toFun := schwartzMultiplier
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [schwartzMultiplier_coe (a + b) u, schwartzMultiplier_coe a u,
      schwartzMultiplier_coe b u, Lp.coeFn_add (schwartzMultiplier a u) (schwartzMultiplier b u)]
      with x hab ha hb hs
    change schwartzMultiplier (a + b) u x = (schwartzMultiplier a u + schwartzMultiplier b u) x
    simp only [hab, hs, Pi.add_apply, ha, hb, add_apply, add_mul]
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [schwartzMultiplier_coe (c • a) u, schwartzMultiplier_coe a u,
      Lp.coeFn_smul c (schwartzMultiplier a u)] with x hca ha hs
    change schwartzMultiplier (c • a) u x = (c • schwartzMultiplier a u) x
    simp only [hca, hs, Pi.smul_apply, ha, smul_apply, smul_eq_mul, mul_assoc]

def dirichletValueMultiplierLinear (K : Set X) :
    𝓢(X, ℝ) →ₗ[ℝ] dirichletValue K →L[ℝ] dirichletValue K where
  toFun := dirichletValueMultiplier K
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    change schwartzMultiplier (a + b) (u : L2) =
      schwartzMultiplier a (u : L2) + schwartzMultiplier b (u : L2)
    exact congrArg (fun L : L2 →L[ℝ] L2 => L (u : L2)) (schwartzMultiplierLinear.map_add a b)
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    change schwartzMultiplier (c • a) (u : L2) = c • schwartzMultiplier a (u : L2)
    exact congrArg (fun L : L2 →L[ℝ] L2 => L (u : L2)) (schwartzMultiplierLinear.map_smul c a)

theorem hasDerivWithinAt_schwartzMultiplier {a b : ℝ} {S : Set X} (hS : IsCompact S)
    (f d : ℝ → 𝓢(X, ℝ))
    (hdf : ∀ t ∈ Icc a b, ∀ x,
      HasDerivWithinAt (fun s => f s x) (d t x) (Icc a b) t)
    (hdc : ContinuousOn (fun p : ℝ × X => d p.1 p.2) (Icc a b ×ˢ S))
    (hfS : ∀ t ∈ Icc a b, ∀ x, x ∉ S → f t x = 0)
    (hdS : ∀ t ∈ Icc a b, ∀ x, x ∉ S → d t x = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => schwartzMultiplier (f s))
      (schwartzMultiplier (d t)) (Icc a b) t := by
  let L : (Unit → 𝓢(X, ℝ)) →ₗ[ℝ] L2 →L[ℝ] L2 :=
    schwartzMultiplierLinear.comp (LinearMap.proj ())
  exact hasDerivWithinAt_coefficientOperator L zero_le_one
    (fun f M hM hf => by
      change ‖schwartzMultiplier (f ())‖ ≤ 1 * M
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ hM (fun u =>
        norm_schwartzMultiplier_le _ u (hf ()))) hS
    (fun s _ => f s) (fun s _ => d s) (fun s hs _ => hdf s hs)
    (continuousOn_pi.mpr (fun _ => hdc)) (fun s hs _ => hfS s hs)
    (fun s hs _ => hdS s hs) ht

theorem hasDerivWithinAt_dirichletValueMultiplier (K : Set X)
    {a b : ℝ} {S : Set X} (hS : IsCompact S) (f d : ℝ → 𝓢(X, ℝ))
    (hdf : ∀ t ∈ Icc a b, ∀ x,
      HasDerivWithinAt (fun s => f s x) (d t x) (Icc a b) t)
    (hdc : ContinuousOn (fun p : ℝ × X => d p.1 p.2) (Icc a b ×ˢ S))
    (hfS : ∀ t ∈ Icc a b, ∀ x, x ∉ S → f t x = 0)
    (hdS : ∀ t ∈ Icc a b, ∀ x, x ∉ S → d t x = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => dirichletValueMultiplier K (f s))
      (dirichletValueMultiplier K (d t)) (Icc a b) t := by
  let L : (Unit → 𝓢(X, ℝ)) →ₗ[ℝ] dirichletValue K →L[ℝ] dirichletValue K :=
    (dirichletValueMultiplierLinear K).comp (LinearMap.proj ())
  exact hasDerivWithinAt_coefficientOperator L zero_le_one
    (fun f M hM hf => by
      change ‖dirichletValueMultiplier K (f ())‖ ≤ 1 * M
      rw [one_mul]
      exact norm_dirichletValueMultiplier_le K _ hM (hf ())) hS
    (fun s _ => f s) (fun s _ => d s) (fun s hs _ => hdf s hs)
    (continuousOn_pi.mpr (fun _ => hdc)) (fun s hs _ => hfS s hs)
    (fun s hs _ => hdS s hs) ht

end PoincareConjecture.M35.Uniqueness.Heat
