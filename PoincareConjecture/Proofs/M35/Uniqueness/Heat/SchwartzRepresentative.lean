import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SchwartzJetRealization
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousCoherentJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open DeTurckHigherDomainNative DeTurckDomainRegularityNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_schwartz_of_all_finite_weak_jets (u : L2)
    {K : Set V} (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (hu : ∀ s, HasFiniteWeakJet u s) :
    ∃ φ : 𝓢(V, ℝ), φ.toLp 2 volume = u ∧ ∀ x ∉ K, φ x = 0 := by
  obtain ⟨f, hf, hfu, hfK⟩ := exists_smooth_of_all_finite_weak_jets u hK huK hu
  have hfc : HasCompactSupport (f : V → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact hK (Function.support_subset_iff'.mpr hfK)
  let φ : 𝓢(V, ℝ) := hfc.toSchwartzMap hf
  refine ⟨φ, ?_, hfK⟩
  apply Lp.ext
  filter_upwards [φ.coeFn_toLp 2 volume, hfu] with x hx hux
  exact hx.trans hux

theorem exists_continuous_schwartz_representative (u : ι → L2)
    {K : Set V} (hK : IsCompact K) (huK : ∀ t, ∀ᵐ x ∂volume, x ∉ K → u t x = 0)
    (hu : ∀ s, HasContinuousWeakJet u s) :
    ∃ φ : ι → 𝓢(V, ℝ), (∀ t, (φ t).toLp 2 volume = u t) ∧
      (∀ t x, x ∉ K → φ t x = 0) ∧
      ∀ w, Continuous (fun t =>
        (orderedSchwartzDerivative w (φ t)).toBoundedContinuousFunction) := by
  choose φ hφ0 hφK using fun t =>
    exists_schwartz_of_all_finite_weak_jets (u t) hK (huK t) (fun s => (hu s).slice t)
  obtain ⟨q, hq0, hq, hqc⟩ := exists_continuous_coherent_weakJet u hu
  refine ⟨φ, hφ0, hφK, ?_⟩
  intro w
  let p := n + 1
  have hp : (n : ℝ) < 2 * (2 * (p : ℝ)) := by
    dsimp only [p]
    push_cast
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  exact continuous_schwartzDerivative_of_weak_jets φ q (2 * p + w.length) p w le_rfl hp
    (fun t => hq t _) (fun t => (hq0 t).trans (hφ0 t).symm) (fun v _ => hqc v)

theorem continuous_initial_schwartz_jets_of_third_weak_jet
    (u : ι → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (φ : ι → 𝓢(EuclideanSpace ℝ (Fin 3), ℝ))
    (hφ : ∀ t, (φ t).toLp 2 volume = u t) (hu : HasContinuousWeakJet u 3)
    (w : List (Fin 3)) (hw : w.length ≤ 1) :
    Continuous (fun t => (orderedSchwartzDerivative w (φ t)).toBoundedContinuousFunction) := by
  obtain ⟨q, hq0, hq, hqc⟩ := hu
  exact continuous_schwartzDerivative_of_weak_jets φ q 3 1 w (by omega) (by norm_num)
    hq (fun t => (hq0 t).trans (hφ t).symm) hqc

end PoincareConjecture.M35.Uniqueness.Heat
