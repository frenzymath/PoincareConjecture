import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawAbsoluteFormTrace
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSpatialJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorSmoothRealization









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff BoundedContinuousFunction

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem exists_actual_raw_compact_heat_spatial_jets {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set X} (hK : IsCompact K) (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    {u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)}
    (hsol : PrincipalValueHeat K
      (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη)
      (fun r => rawLowerFormOperator (F.connection r) hK.isClosed η hη) a (b - a) u₀ v U) :
    ∃ W : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ W t) ∧
      (∀ t ∈ Ioo a b, finiteHilbertMap (dirichletInclusion K) (W t) = U (t - a)) ∧
      (∀ t ∈ Ioo a b, ∀ s j k, HasInteriorWeakJets K (iteratedDeriv j W t k) s) ∧
      (∀ t ∈ Ioo a b, ∀ j k, ∀ χ : 𝓢(X, ℝ), HasCompactSupport χ →
        tsupport χ ⊆ interior K → ∃ f : X →ᵇ ℝ, ContDiff ℝ ∞ (f : X → ℝ) ∧
          (f : X → ℝ) =ᵐ[volume] localizedDirichletValue K χ (iteratedDeriv j W t k) ∧
          ∀ x ∉ tsupport χ, f x = 0) := by
  have htrace : ∃ W : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ W t) ∧
      (∀ t ∈ Ioo a b, finiteHilbertMap (dirichletInclusion K) (W t) = U (t - a)) ∧
      (∀ t ∈ Ioo a b, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (finiteHilbertMap (dirichletInclusion K) (deriv W t)) =
            inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
              (rawLowerFormOperator (F.connection t) hK.isClosed η hη (W t)) -
                principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη)
                  z (W t)) :=
    exists_raw_compact_absolute_form_trace F hab hJ hK η hη hηK hsol
  obtain ⟨W, hw, hg, he⟩ := htrace
  have hj (t : ℝ) (ht : t ∈ Ioo a b) (s j : ℕ) (k : Fin n) :
      HasInteriorWeakJets K (iteratedDeriv j W t k) s :=
    (raw_compact_heat_all_spatial_jets F hab hJ hK η hη hηK W hw he ht s j k).mono
      (Nat.le_succ s)
  refine ⟨W, hw, hg, hj, ?_⟩
  intro t ht j k χ hχ hχK
  exact exists_smooth_localized_dirichlet_field K (iteratedDeriv j W t k)
    (fun s => hj t ht s j k) χ hχ hχK

end PoincareConjecture.M35.Uniqueness.Heat
