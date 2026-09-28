import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawFormRecovery
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawInteriorThird









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_raw_compact_heat_everytime_thirdJets {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    {u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)}
    (hsol : PrincipalValueHeat K
      (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη)
      (fun r => rawLowerFormOperator (F.connection r) hK.isClosed η hη) a (b - a) u₀ v U) :
    ∃ w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ t ∈ Ioo 0 (b - a), ContDiffAt ℝ ∞ w t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 (b - a)), w t = v t) ∧
      (∀ t ∈ Ioo 0 (b - a), finiteHilbertMap (dirichletInclusion K) (w t) = U t) ∧
      ∀ t ∈ Ioo 0 (b - a), ∀ χ : 𝓢(V, ℝ), HasCompactSupport χ →
        tsupport χ ⊆ interior K → ∀ k : Fin n,
        ∃ q : List (Fin n) → L2, q [] = localizedDirichletValue K χ (w t k) ∧
          (∀ i, q [i] = localizedDirichletPartial K χ (w t k) i) ∧ IsWeakSchwartzJet q 3 := by
  have hrec : ∃ w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ t ∈ Ioo 0 (b - a), ContDiffAt ℝ ∞ w t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 (b - a)), w t = v t) ∧
      (∀ t ∈ Ioo 0 (b - a), finiteHilbertMap (dirichletInclusion K) (w t) = U t) ∧
      (∀ t ∈ Ioo 0 (b - a),
        finiteHilbertMap (dirichletInclusion K) (deriv w t) = deriv U t) ∧
      (∀ t ∈ Ioo 0 (b - a), ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (deriv U t) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection (a + t)) hK.isClosed η hη (w t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη)
                z (w t)) :=
    exists_raw_compact_vector_heat_smooth_form F hab hJ hK η hη hηK hsol
  obtain ⟨w, hw, hae, hg, hd, he⟩ := hrec
  refine ⟨w, hw, hae, hg, ?_⟩
  intro t ht χ hχ hχK k
  apply exists_raw_compact_heat_interior_thirdJet (F.connection (a + t)) hK η hη hηK
    (w t) (deriv w t) _ χ hχ hχK k
  intro z
  have hinner : inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
      (finiteHilbertMap (dirichletInclusion K) (deriv w t)) =
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (deriv U t) :=
    congrArg (fun q : PiLp 2 (fun _ : Fin n => dirichletValue K) =>
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) q) (hd t ht)
  exact hinner.trans (he t ht z)

end PoincareConjecture.M35.Uniqueness.Heat
