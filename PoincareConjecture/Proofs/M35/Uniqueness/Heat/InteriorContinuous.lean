import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawInteriorRegularity
import PoincareConjecture.Proofs.M03.Existence.DeTurckMetricDomainNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckHigherDomainNative DeTurckMetricDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_continuous_localized_dirichlet_field (hn : (n : ℝ) < 4)
    (K : Set V) (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (u : dirichletForm K)
    (W : Fin n → Fin n → L2)
    (hW : ∀ i j, HasWeakSchwartzDerivative (localizedDirichletPartial K χ u i)
      (W i j) (EuclideanSpace.single j (1 : ℝ))) :
    ∃ f : V →ᵇ ℝ, (f : V → ℝ) =ᵐ[volume] localizedDirichletValue K χ u ∧
      ∀ x ∉ tsupport χ, f x = 0 := by
  let q : List (Fin n) → L2
    | [] => localizedDirichletValue K χ u
    | [i] => localizedDirichletPartial K χ u i
    | i :: j :: _ => W j i
  have hq : IsWeakSchwartzJet q 2 := by
    intro w hw i
    cases w with
    | nil => exact localizedDirichletPartial_weak K χ u i
    | cons j w =>
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hw
        omega)
      subst w
      exact hW j i
  have hdim : (n : ℝ) < 2 * (2 * ((1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_one, mul_one, show (2 : ℝ) * 2 = 4 by norm_num] using hn
  have hqK : ∀ᵐ x ∂volume, x ∉ tsupport χ → q [] x = 0 :=
    localizedDirichletValue_ae_support K χ u
  refine ⟨finiteJetContinuous 2 1 [] (by simp) hdim (fun v => q (List.ofFn v.2)),
    finiteJetContinuous_ae_eq q 2 1 [] (by simp) hdim hq hχ hqK, ?_⟩
  intro x hx
  exact finiteJetContinuous_zero_off q 2 1 [] (by simp) hdim hq hχ hqK hx

theorem raw_compact_heat_component_continuous
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    {K : Set StandardCapSpace} (hK : IsCompact K)
    (η : 𝓢(StandardCapSpace, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    (u : PiLp 2 (fun _ : Fin 3 => dirichletForm K))
    (Z : PiLp 2 (fun _ : Fin 3 => dirichletValue K))
    (heq : ∀ z : PiLp 2 (fun _ : Fin 3 => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) Z =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (rawLowerFormOperator D hK.isClosed η hη u) -
            principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη) z u)
    (χ : 𝓢(StandardCapSpace, ℝ)) (hχ : HasCompactSupport χ)
    (hχK : tsupport χ ⊆ interior K) (k : Fin 3) :
    ∃ f : StandardCapSpace →ᵇ ℝ,
      (f : StandardCapSpace → ℝ) =ᵐ[volume] localizedDirichletValue K χ (u k) ∧
        ∀ x ∉ tsupport χ, f x = 0 := by
  obtain ⟨W, hW⟩ := exists_raw_compact_heat_interior_secondDerivatives D hK η hη hηK
    u Z heq χ hχ hχK k
  exact exists_continuous_localized_dirichlet_field (by norm_num : (3 : ℝ) < 4) K χ hχ (u k) W hW

end PoincareConjecture.M35.Uniqueness.Heat
