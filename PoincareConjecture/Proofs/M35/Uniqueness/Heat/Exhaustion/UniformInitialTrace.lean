import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.AdjointCarrier
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TestPair
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TestedIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def supportedTestInclusion {E K : Set V} (hEK : E ⊆ K)
    (f : supportedTests E) : supportedTests K :=
  ⟨f, fun x hx => f.property x (fun he => hx (hEK he))⟩

theorem exists_raw_fixed_test_initial_bound {J : Set ℝ} (F : RicciFlow n V J)
    {T : ℝ} (hJ : Icc 0 T ⊆ J) {E : Set V} (hE : IsCompact E)
    (f : Fin n → supportedTests E) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (K : Set V) (hK : IsClosed K) (_hEK : E ⊆ K)
      (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (_hηK : ∀ x ∈ K, η x = 1)
      (u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K))
      (v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
      (U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)),
      PrincipalValueHeat K (fun t => rawCutoffPrincipalCoefficient (F.metric t) η hη)
        (fun t => rawLowerFormOperator (F.connection t) hK η hη) 0 T u₀ v U →
      (∀ t ∈ Icc 0 T, ∀ᵐ x ∂volume, x ∈ K →
        (F.metric t).inner x (dirichletValueField K (U t) x)
          (dirichletValueField K (U t) x) ≤ Q) →
      ∀ t ∈ Icc 0 T,
      ‖(∫ x, inner ℝ (schwartzField (fun j => (f j : 𝓢(V, ℝ))) x)
          (dirichletValueField K (U t) x)) -
        (∫ x, inner ℝ (schwartzField (fun j => (f j : 𝓢(V, ℝ))) x)
          (dirichletValueField K u₀ x))‖ ≤ M * t := by
  obtain ⟨c, hc, hlower⟩ := exists_raw_metric_slab_lower_bound F isCompact_Icc hJ hE
  obtain ⟨S, hS, htest⟩ := exists_raw_adjoint_carrier_bound F isCompact_Icc hJ hE f
  let N : ℝ := 1 + Q / c
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  refine ⟨(S * N) * volume.real E, by positivity, ?_⟩
  intro K hK hEK η hη hηK u₀ v U hsol hmax t ht
  let fK : Fin n → supportedTests K := fun j => supportedTestInclusion hEK (f j)
  have hb (s : ℝ) (hs : s ∈ Icc 0 T) :
      ‖inner ℝ (vectorTestValue K (vectorTestAdjoint hK
        (rawCutoffPrincipalCoefficient (F.metric s) η hη)
        (rawCutoffFirstComponent (F.connection s) η hη)
        (rawCutoffZeroComponent (F.connection s) η hη) fK)) (U s)‖ ≤
          (S * N) * volume.real E := by
    let adj := vectorTestAdjoint hK (rawCutoffPrincipalCoefficient (F.metric s) η hη)
      (rawCutoffFirstComponent (F.connection s) η hη)
      (rawCutoffZeroComponent (F.connection s) η hη) fK
    have he : schwartzField (fun j => (adj j : 𝓢(V, ℝ))) =
        rawTestAdjointField (F.connection s) (fun j => (f j : 𝓢(V, ℝ))) := by
      funext x
      rw [schwartzField_apply]
      apply PiLp.ext
      exact fun j => raw_vectorTestAdjoint_apply hK (F.connection s) η hη hηK fK j x
    have hu : ∀ᵐ x ∂volume, x ∈ E → ‖dirichletValueField K (U s) x‖ ≤ N := by
      apply metric_bound_euclidean_bound (F.metric s) hc hQ (hlower s hs)
      filter_upwards [hmax s hs] with x hx
      exact fun hxE => hx (hEK hxE)
    apply vectorTestValue_pair_bound K adj (U s) hE
    · intro x hx
      rw [he]
      exact rawTestAdjointField_zero_off hE.isClosed (F.connection s) f hx
    · intro x hx
      rw [he]
      exact htest s hs x hx
    · exact hu
  have hout := principalValueHeat_test_initial_bound hK
    (fun s => rawCutoffPrincipalCoefficient (F.metric s) η hη)
    (fun s => rawCutoffFirstComponent (F.connection s) η hη)
    (fun s => rawCutoffZeroComponent (F.connection s) η hη)
    (fun s => rawCutoffPrincipalCoefficient_symmetric (F.metric s) η hη) hsol fK
    hb ht
  simpa only [vectorTestValue_pair_integral, fK, supportedTestInclusion] using hout

end PoincareConjecture.M35.Uniqueness.Heat
