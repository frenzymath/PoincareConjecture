import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorFiniteJets
import PoincareConjecture.Proofs.M03.Existence.DeTurckMetricDomainNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanSobolevRegularityNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckHigherDomainNative DeTurckMetricDomainNative
  EuclideanSobolevContinuousNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_contDiff_of_finite_weak_jets (u : L2) (k : ℕ)
    {K : Set V} (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (hu : HasFiniteWeakJet u (2 * (k + n + 1))) :
    ∃ f : V →ᵇ ℝ, ContDiff ℝ k (f : V → ℝ) ∧ (f : V → ℝ) =ᵐ[volume] u ∧
      ∀ x ∉ K, f x = 0 := by
  obtain ⟨q, hq0, hq⟩ := hu
  have hp : (n : ℝ) < 2 * (2 * ((k + n + 1 : ℕ) : ℝ)) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ k by positivity, show (0 : ℝ) ≤ n by positivity]
  have hpk : (n : ℝ) < 2 * (2 * ((k + n + 1 : ℕ) : ℝ) - k) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ k by positivity, show (0 : ℝ) ≤ n by positivity]
  let f := finiteJetContinuous (2 * (k + n + 1)) (k + n + 1) [] (by simp) hp
    (fun v => q (List.ofFn v.2))
  have hqK : ∀ᵐ x ∂volume, x ∉ K → q [] x = 0 := by simpa only [hq0] using huK
  refine ⟨f, contDiff_realSobolevRealization k hp hpk _, ?_, ?_⟩
  · simpa only [hq0] using finiteJetContinuous_ae_eq q (2 * (k + n + 1))
      (k + n + 1) [] (by simp) hp hq hK hqK
  · exact fun _x hx => finiteJetContinuous_zero_off q (2 * (k + n + 1))
      (k + n + 1) [] (by simp) hp hq hK hqK hx

theorem exists_smooth_of_all_finite_weak_jets (u : L2)
    {K : Set V} (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (hu : ∀ s, HasFiniteWeakJet u s) :
    ∃ f : V →ᵇ ℝ, ContDiff ℝ ∞ (f : V → ℝ) ∧ (f : V → ℝ) =ᵐ[volume] u ∧
      ∀ x ∉ K, f x = 0 := by
  choose f hf hae hsupport using fun k => exists_contDiff_of_finite_weak_jets u k hK huK
    (hu (2 * (k + n + 1)))
  refine ⟨f 0, contDiff_infty.mpr ?_, hae 0, hsupport 0⟩
  intro k
  have he : (f 0 : V → ℝ) = f k :=
    ((f 0).continuous.ae_eq_iff_eq volume (f k).continuous).mp ((hae 0).trans (hae k).symm)
  exact he.symm ▸ hf k

theorem exists_smooth_localized_dirichlet_field (K : Set V) (u : dirichletForm K)
    (hu : ∀ s, HasInteriorWeakJets K u s) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) :
    ∃ f : V →ᵇ ℝ, ContDiff ℝ ∞ (f : V → ℝ) ∧
      (f : V → ℝ) =ᵐ[volume] localizedDirichletValue K χ u ∧
      ∀ x ∉ tsupport χ, f x = 0 :=
  exists_smooth_of_all_finite_weak_jets (localizedDirichletValue K χ u) hχ
    (localizedDirichletValue_ae_support K χ u) (fun s => hu s χ hχ hχK)

end PoincareConjecture.M35.Uniqueness.Heat
