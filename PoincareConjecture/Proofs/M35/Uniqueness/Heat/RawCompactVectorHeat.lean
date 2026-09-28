import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalVectorMixed
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCompactHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawLowerContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_raw_compact_vector_heat {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) (hηK : ∀ x ∈ K, η x = 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ a + τ < b ∧
      ∀ v₀ : PiLp 2 (fun _ : Fin n => dirichletForm K),
      ∃ (v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
        (U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)),
        MemLp v 2 (timeMeasure τ) ∧ U 0 = finiteHilbertMap (dirichletInclusion K) v₀ ∧
        ContinuousOn U (Icc 0 τ) ∧
        (∀ᵐ t ∂timeMeasure τ, finiteHilbertMap (dirichletInclusion K) (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure τ, ∀ w : PiLp 2 (fun _ : Fin n => dirichletForm K),
          HasDerivWithinAt (fun s => inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U s))
            (inner ℝ (finiteHilbertMap (dirichletInclusion K) w)
              (rawLowerFormOperator (F.connection (a + t)) hK.isClosed η hη (v t)) -
                principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη)
                  w (v t)) (Icc 0 τ) t) := by
  let A := fun t => rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη
  let L := fun t => rawLowerFormOperator (F.connection (a + t)) hK.isClosed η hη
  refine (exists_rawCutoffPrincipalCoefficient_ellipticity (F.metric a) hK η hη hηK).elim ?_
  intro ell he
  have hEll : 0 < ell := he.1
  have hell := he.2
  have hA0 : A 0 = rawCutoffPrincipalCoefficient (F.metric a) η hη := by simp only [A, add_zero]
  have hshift : MapsTo (fun t : ℝ => a + t) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2]
  have hAc : ContinuousOn (fun t => principalFormOperator K (A t)) (Icc 0 (b - a)) :=
    (continuousOn_raw_principalFormOperator F isCompact_Icc hJ K η hη hη1).comp
      (continuous_const.add continuous_id).continuousOn hshift
  have hLc : ContinuousOn L (Icc 0 (b - a)) :=
    (continuousOn_rawLowerFormOperator F isCompact_Icc hJ hK.isClosed η hη hη1).comp
      (continuous_const.add continuous_id).continuousOn hshift
  have hsymm : ∀ i j x, A 0 i j x = A 0 j i x := by
    rw [hA0]
    exact rawCutoffPrincipalCoefficient_symmetric (F.metric a) η hη
  have hell0 : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j := by
    rw [hA0]
    exact hell
  refine (exists_principal_vector_mixed_initial_heat hK A hEll (sub_pos.mpr hab)
    hsymm hell0 hAc L hLc).elim ?_
  intro τ hτ
  exact ⟨τ, hτ.1, hτ.2.1, by linarith only [hτ.2.2.1], hτ.2.2.2⟩

end PoincareConjecture.M35.Uniqueness.Heat
