import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalContinuousHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawPrincipalContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem rawCutoffPrincipalCoefficient_symmetric (g : RiemannianMetric n V)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (i j : Fin n) (x : V) :
    rawCutoffPrincipalCoefficient g η hη i j x =
      rawCutoffPrincipalCoefficient g η hη j i x := by
  rw [rawCutoffPrincipalCoefficient_apply, rawCutoffPrincipalCoefficient_apply]
  congr 1
  exact (Matrix.isHermitian_iff_isSymm.mp
    (rawCoordinateGram_posDef g x).inv.isHermitian).apply j i

theorem exists_rawCutoffPrincipalCoefficient_ellipticity (g : RiemannianMetric n V)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤
        ∑ i, ∑ j, rawCutoffPrincipalCoefficient g η hη i j x * ξ i * ξ j := by
  obtain ⟨A, ell, hEll, _, hAK, hell⟩ := exists_raw_principal_schwartz_coefficients g hK
  refine ⟨ell, hEll, ?_⟩
  intro x hx ξ
  simpa only [rawCutoffPrincipalCoefficient_apply, hηK x hx, one_mul, hAK _ _ x hx]
    using hell x hx ξ

theorem exists_raw_compact_principal_heat {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) (hηK : ∀ x ∈ K, η x = 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ a + τ < b ∧
      ∀ P : ℝ → dirichletForm K, MemLp P 2 (timeMeasure τ) →
      ∃ (v : ℝ → dirichletForm K) (U : ℝ → dirichletValue K),
        MemLp v 2 (timeMeasure τ) ∧ U 0 = 0 ∧ ContinuousOn U (Icc 0 τ) ∧
        (∀ᵐ t ∂timeMeasure τ, dirichletInclusion K (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure τ, ∀ w : dirichletForm K,
          HasDerivWithinAt (fun s => inner ℝ (dirichletInclusion K w) (U s))
            (inner ℝ w (P t) - principalEnergy K
              (rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη) w (v t))
            (Icc 0 τ) t) := by
  let A := fun t => rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη
  obtain ⟨ell, hEll, hell⟩ :=
    exists_rawCutoffPrincipalCoefficient_ellipticity (F.metric a) hK η hη hηK
  have hA0 : A 0 = rawCutoffPrincipalCoefficient (F.metric a) η hη := by simp only [A, add_zero]
  have hAc : ContinuousOn (fun t => principalFormOperator K (A t)) (Icc 0 (b - a)) := by
    have hc := continuousOn_raw_principalFormOperator F isCompact_Icc hJ K η hη hη1
    apply hc.comp (continuous_const.add continuous_id).continuousOn
    intro t ht
    change a + t ∈ Icc a b
    constructor <;> linarith only [ht.1, ht.2]
  have hsymm : ∀ i j x, A 0 i j x = A 0 j i x := by
    rw [hA0]
    exact rawCutoffPrincipalCoefficient_symmetric (F.metric a) η hη
  have hell0 : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j := by
    rw [hA0]
    exact hell
  refine (exists_continuous_principal_heat hK A hEll hsymm hell0 (sub_pos.mpr hab) hAc).elim ?_
  intro τ hτ
  exact ⟨τ, hτ.1, hτ.2.1, by linarith only [hτ.2.2.1], hτ.2.2.2⟩

end PoincareConjecture.M35.Uniqueness.Heat
