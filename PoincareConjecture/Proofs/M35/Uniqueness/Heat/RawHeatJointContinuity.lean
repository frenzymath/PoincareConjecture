import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawHeatSecondJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff BoundedContinuousFunction

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckHigherDomainNative DeTurckMetricDomainNative
  ValueInitial

local notation "X" => EuclideanSpace ℝ (Fin 3)
local notation "L2" => Lp ℝ 2 (volume : Measure X)

theorem exists_raw_heat_continuous_smooth_representative
    {J : Set ℝ} (F : RicciFlow 3 X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsCompact K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    {u₀ : PiLp 2 (fun _ : Fin 3 => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin 3 => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin 3 => dirichletValue K)}
    (hsol : PrincipalValueHeat K
      (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη)
      (fun r => rawLowerFormOperator (F.connection r) hK.isClosed η hη) a (b - a) u₀ v U)
    (χ : 𝓢(X, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (k : Fin 3) :
    ∃ f : Ioo a b → X →ᵇ ℝ, Continuous f ∧
      (∀ t, ContDiff ℝ ∞ (f t : X → ℝ)) ∧
      (∀ t, (f t : X → ℝ) =ᵐ[volume]
        schwartzMultiplier χ (U ((t : ℝ) - a) k : L2)) ∧
      ∀ t x, x ∉ tsupport χ → f t x = 0 := by
  obtain ⟨W, hW, hgraph, heq⟩ :=
    exists_raw_compact_absolute_form_trace F hab hJ hK η hη hηK hsol
  obtain ⟨q, hq0, _hq1, hq, hqc⟩ :=
    raw_heat_coherent_secondJets_continuous F hab hJ hK η hη hηK W hW heq χ hχ hχK k
  have hp : (3 : ℝ) < 2 * (2 * ((1 : ℕ) : ℝ)) := by norm_num
  let f : Ioo a b → X →ᵇ ℝ := fun t =>
    finiteJetContinuous 2 1 [] (by simp) hp (fun j => q t (List.ofFn j.2))
  have hf : Continuous f := by
    apply (finiteJetContinuous 2 1 [] (by simp) hp).continuous.comp
    apply continuous_pi
    intro j
    exact hqc (List.ofFn j.2) (by
      simpa only [List.length_ofFn] using Nat.le_of_lt_succ j.1.isLt)
  have hsupport (t : Ioo a b) : ∀ᵐ x ∂volume, x ∉ tsupport χ → q t [] x = 0 := by
    rw [hq0]
    exact localizedDirichletValue_ae_support K χ (W t k)
  have hae (t : Ioo a b) : (f t : X → ℝ) =ᵐ[volume] q t [] :=
    finiteJetContinuous_ae_eq (q t) 2 1 [] (by simp) hp (hq t 2) hχ (hsupport t)
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨g, hg, hga, _hgs⟩ := exists_smooth_of_all_finite_weak_jets
      (q t []) hχ (hsupport t) (fun s => ⟨q t, rfl, hq t s⟩)
    have he : (f t : X → ℝ) = g :=
      ((f t).continuous.ae_eq_iff_eq volume g.continuous).mp ((hae t).trans hga.symm)
    rw [he]
    exact hg
  · intro t
    have hcomponent : dirichletInclusion K (W t k) = U ((t : ℝ) - a) k :=
      congrArg (fun z : PiLp 2 (fun _ : Fin 3 => dirichletValue K) => z k)
        (hgraph t t.property)
    simpa only [hq0, localizedDirichletValue, hcomponent] using hae t
  · intro t x hx
    exact finiteJetContinuous_zero_off (q t) 2 1 [] (by simp) hp (hq t 2) hχ (hsupport t) hx

end PoincareConjecture.M35.Uniqueness.Heat
