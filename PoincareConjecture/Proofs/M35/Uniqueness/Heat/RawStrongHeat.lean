import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalTestHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawOperatorSmooth
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCompactHeat










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_raw_strong_compact_vector_heat {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ a + τ < b ∧
      ∀ f : Fin n → supportedTests K,
      ∃ (u : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
        (Z : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)),
        u 0 = vectorTestForm K f ∧
        ContinuousOn u (Icc 0 τ) ∧ ContinuousOn Z (Icc 0 τ) ∧
        (∀ t ∈ Icc 0 τ, HasDerivWithinAt
          (fun s => finiteHilbertMap (dirichletInclusion K) (u s)) (Z t) (Icc 0 τ) t) ∧
        (∀ t ∈ Icc 0 τ, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (Z t) =
            inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
              (rawLowerFormOperator (F.connection (a + t)) hK.isClosed η hη (u t)) -
                principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη)
                  z (u t)) ∧
        ∃ w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
          MemLp w 2 (SpectralHeatNative.timeMeasure τ) ∧
          ∀ᵐ t ∂SpectralHeatNative.timeMeasure τ,
            HasDerivAt u (w t) t ∧ finiteHilbertMap (dirichletInclusion K) (w t) = Z t := by
  let A := fun t => rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη
  let L := fun t => rawLowerFormOperator (F.connection (a + t)) hK.isClosed η hη
  refine (exists_rawCutoffPrincipalCoefficient_ellipticity (F.metric a) hK η hη hηK).elim ?_
  intro ell he
  have hEll : 0 < ell := he.1
  have hell := he.2
  have hA0 : A 0 = rawCutoffPrincipalCoefficient (F.metric a) η hη := by
    simp only [A, add_zero]
  have hshift : MapsTo (fun t : ℝ => a + t) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2]
  have hAc : ContDiffOn ℝ 1 (fun t => principalFormOperator K (A t)) (Icc 0 (b - a)) :=
    ((contDiffOn_raw_principalFormOperator F hab hJ K η hη).of_le (by simp)).comp
      (contDiffOn_const.add contDiffOn_id) hshift
  have hLc : ContDiffOn ℝ 1 L (Icc 0 (b - a)) :=
    ((contDiffOn_rawLowerFormOperator F hab hJ hK.isClosed η hη).of_le (by simp)).comp
      (contDiffOn_const.add contDiffOn_id) hshift
  have hsymm : ∀ i j x, A 0 i j x = A 0 j i x := by
    rw [hA0]
    exact rawCutoffPrincipalCoefficient_symmetric (F.metric a) η hη
  have hell0 : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j := by
    rw [hA0]
    exact hell
  refine (exists_principal_test_heat hK A
    (fun t => rawCutoffFirstComponent (F.connection (a + t)) η hη)
    (fun t => rawCutoffZeroComponent (F.connection (a + t)) η hη)
    hEll (sub_pos.mpr hab) hsymm hell0 hAc hLc).elim ?_
  intro τ hτ
  exact ⟨τ, hτ.1, hτ.2.1, by linarith only [hτ.2.2.1], hτ.2.2.2⟩

end PoincareConjecture.M35.Uniqueness.Heat
