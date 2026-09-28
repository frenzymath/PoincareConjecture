import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousWeakJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def HasContinuousInteriorJets (K : Set V) (u : ι → dirichletForm K) (s : ℕ) : Prop :=
  ∀ χ : 𝓢(V, ℝ), HasCompactSupport χ → tsupport χ ⊆ interior K →
    HasContinuousWeakJet (fun t => localizedDirichletValue K χ (u t)) s

theorem HasContinuousInteriorJets.mono {K : Set V} {u : ι → dirichletForm K} {s r : ℕ}
    (hu : HasContinuousInteriorJets K u s) (hrs : r ≤ s) : HasContinuousInteriorJets K u r :=
  fun χ hχ hχK => (hu χ hχ hχK).mono hrs

theorem HasContinuousInteriorJets.slice {K : Set V} {u : ι → dirichletForm K} {s : ℕ}
    (hu : HasContinuousInteriorJets K u s) (t : ι) : HasInteriorWeakJets K (u t) s :=
  fun χ hχ hχK => (hu χ hχ hχK).slice t

theorem hasContinuousInteriorJets_one {K : Set V} (u : ι → dirichletForm K)
    (hu : Continuous u) : HasContinuousInteriorJets K u 1 := by
  intro χ _ _
  let q : ι → List (Fin n) → L2 := fun t w => match w with
    | [] => localizedDirichletValue K χ (u t)
    | i :: _ => localizedDirichletPartial K χ (u t) i
  refine ⟨q, fun _ => rfl, ?_, ?_⟩
  · intro t w hw i
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst w
    exact localizedDirichletPartial_weak K χ (u t) i
  · intro w _hw
    cases w with
    | nil =>
      simpa only [q, localizedDirichletValue, Function.comp_def,
        ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
        (schwartzMultiplier χ).continuous.comp
          (((dirichletValue K).subtypeL.comp (dirichletInclusion K)).continuous.comp hu)
    | cons i w =>
      simpa only [q, localizedDirichletPartial, Function.comp_def, Pi.add_def,
        ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
        ((schwartzMultiplier χ).continuous.comp ((dirichletPartial K i).continuous.comp hu)).add
          ((schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ)).continuous.comp
            (((dirichletValue K).subtypeL.comp (dirichletInclusion K)).continuous.comp hu))

theorem HasContinuousInteriorJets.partial_product
    {K : Set V} {u : ι → dirichletForm K} {s : ℕ}
    (hu : HasContinuousInteriorJets K u (s + 1)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) (i : Fin n) :
    HasContinuousWeakJet (fun t => schwartzMultiplier χ (dirichletPartial K i (u t))) s := by
  obtain ⟨d, hd, hdjet⟩ := (hu χ hχ hχK).exists_derivative i
  have hdactual (t : ι) : d t = localizedDirichletPartial K χ (u t) i :=
    (hd t).unique (localizedDirichletPartial_weak K χ (u t) i)
  have hχd : HasCompactSupport
      ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) :=
    hχ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
  have hχdK : tsupport ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) ⊆
      interior K := (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hχK
  have hcut := (hu (∂_{EuclideanSpace.single i (1 : ℝ)} χ) hχd hχdK).mono (Nat.le_succ s)
  simpa only [hdactual, localizedDirichletPartial, localizedDirichletValue,
    add_sub_cancel_right] using hdjet.sub hcut

end PoincareConjecture.M35.Uniqueness.Heat
