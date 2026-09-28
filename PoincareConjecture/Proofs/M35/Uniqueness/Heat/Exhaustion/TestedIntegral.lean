import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TestAdjoint
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalSegment








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial SpectralHeatNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem principalValueHeat_adjoint_integral {K : Set V} (hK : IsClosed K)
    (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (B : ℝ → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : ℝ → Fin m → Fin m → 𝓢(V, ℝ))
    (hA : ∀ s i j x, A s i j x = A s j i x) {r T : ℝ}
    {u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)}
    (hsol : PrincipalValueHeat K A (fun s => dirichletVectorLowerOrder hK (B s) (C s))
      r T u₀ v U) (f : Fin m → supportedTests K) {t : ℝ} (ht : t ∈ Icc 0 T) :
    inner ℝ (vectorTestValue K f) (U t) = inner ℝ (vectorTestValue K f) u₀ +
      ∫ s in (0 : ℝ)..t,
        inner ℝ (vectorTestValue K (vectorTestAdjoint hK (A (r + s))
          (B (r + s)) (C (r + s)) f)) (U s) := by
  have he := hsol.2.2.2.2.2 t ht (vectorTestForm K f)
  simp only [vectorTest_inclusion] at he
  refine he.trans (congrArg (fun z : ℝ => inner ℝ (vectorTestValue K f) u₀ + z) ?_)
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2)
    hsol.2.2.2.1] with s hs
  exact (vectorTestAdjoint_pair hK (A (r + s)) (hA (r + s)) (B (r + s))
    (C (r + s)) f (v s)).trans
      (congrArg (fun w => inner ℝ (vectorTestValue K (vectorTestAdjoint hK
        (A (r + s)) (B (r + s)) (C (r + s)) f)) w) hs)

theorem principalValueHeat_test_initial_bound {K : Set V} (hK : IsClosed K)
    (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (B : ℝ → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : ℝ → Fin m → Fin m → 𝓢(V, ℝ))
    (hA : ∀ s i j x, A s i j x = A s j i x) {T : ℝ}
    {u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)}
    (hsol : PrincipalValueHeat K A (fun s => dirichletVectorLowerOrder hK (B s) (C s))
      0 T u₀ v U) (f : Fin m → supportedTests K) {M : ℝ}
    (hb : ∀ s ∈ Icc 0 T, ‖inner ℝ (vectorTestValue K (vectorTestAdjoint hK (A s)
      (B s) (C s) f)) (U s)‖ ≤ M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖inner ℝ (vectorTestValue K f) (U t) - inner ℝ (vectorTestValue K f) u₀‖ ≤ M * t := by
  rw [principalValueHeat_adjoint_integral hK A B C hA hsol f ht, add_sub_cancel_left]
  simp only [zero_add]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (fun s hs => hb s (by
      rw [uIoc_of_le ht.1] at hs
      exact ⟨hs.1.le, hs.2.trans ht.2⟩))
  simpa only [sub_zero, abs_of_nonneg ht.1] using h

end PoincareConjecture.M35.Uniqueness.Heat
