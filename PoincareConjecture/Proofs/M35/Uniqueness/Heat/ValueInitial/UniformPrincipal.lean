import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalSegment
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.UniformStep









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_uniform_principal_value_restart
    {K : Set V} (hK : IsCompact K) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    {ell a b : ℝ} (hell : 0 < ell)
    (hA : ∀ r ∈ Icc a b, ∀ i j x, A r i j x = A r j i x)
    (hEll : ∀ r ∈ Icc a b, ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A r i j x * ξ i * ξ j)
    (hAc : ContinuousOn (fun t => principalFormOperator K (A t)) (Icc a b))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K))
    (hLc : ContinuousOn L (Icc a b)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∀ r ∈ Icc a b, ∀ T ∈ Icc 0 τ, r + T ≤ b →
      ∀ u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K),
      ∃ (v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K))
        (U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)),
        PrincipalValueHeat K A L r T u₀ v U := by
  let P : ℝ → dirichletForm K →L[ℝ] dirichletForm K :=
    fun t => principalFormOperator K (A t)
  let c := min 1 ell
  have hc : 0 < c := lt_min zero_lt_one hell
  let M := c⁻¹
  have hM : 0 < M := inv_pos.mpr hc
  have hM1 : 1 ≤ M := (one_le_inv₀ hc).mpr (min_le_left _ _)
  have hscale : 1 ≤ min 1 ell * M ^ 2 := by
    calc
      1 = c * M := (mul_inv_cancel₀ hc.ne').symm
      _ ≤ (c * M) * M := le_mul_of_one_le_right (by positivity) hM1
      _ = min 1 ell * M ^ 2 := by dsimp only [c]; ring
  obtain ⟨q, C, τ, hq, hC, hτ, hτ1, hPb, hLb, hsmall⟩ :=
    exists_uniform_mixed_step hM P hAc L hLc
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro r hr T hT hTb u₀
  have hshift : MapsTo (fun t : ℝ => r + t) (Icc 0 T) (Icc a b) := by
    intro t ht
    constructor <;> linarith only [hr.1, ht.1, ht.2, hTb]
  have hPc : ContinuousOn (fun t => P (r + t)) (Icc 0 T) :=
    hAc.comp (continuous_const.add continuous_id).continuousOn hshift
  have hLl : ContinuousOn (fun t => L (r + t)) (Icc 0 T) :=
    hLc.comp (continuous_const.add continuous_id).continuousOn hshift
  have hAb : ∀ t ∈ Icc 0 T, ‖P (r + 0) - P (r + t)‖ ≤ q := by
    intro t ht
    rw [add_zero]
    apply hPb r hr (r + t) (hshift ht)
    rw [show r - (r + t) = -t by ring, abs_neg, abs_of_nonneg ht.1]
    exact ht.2.trans hT.2
  have hsymm : ∀ i j x, A (r + 0) i j x = A (r + 0) j i x := by
    simpa only [add_zero] using hA r hr
  have hell0 : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A (r + 0) i j x * ξ i * ξ j := by
    simpa only [add_zero] using hEll r hr
  exact exists_principal_vector_value_initial_heat hK (fun t => A (r + t))
    hell hT.1 hM.le hq.le hC.le hscale hsymm hell0 hPc hAb
    (fun t => L (r + t)) hLl (fun t ht => hLb (r + t) (hshift ht)) (hsmall T hT) u₀

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
