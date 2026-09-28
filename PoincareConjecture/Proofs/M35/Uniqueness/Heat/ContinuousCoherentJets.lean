import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousWeakJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorCoherentJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat

open DeTurckHigherDomainNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_continuous_coherent_weakJet (u : ι → L2)
    (hu : ∀ s, HasContinuousWeakJet u s) :
    ∃ q : ι → List (Fin n) → L2, (∀ t, q t [] = u t) ∧
      (∀ t s, IsWeakSchwartzJet (q t) s) ∧
      ∀ w, Continuous (fun t => q t w) := by
  choose q hq0 hq using fun t => exists_coherent_weakJet (u t) (fun s => (hu s).slice t)
  refine ⟨q, hq0, hq, ?_⟩
  intro w
  obtain ⟨p, hp0, hp, hpc⟩ := hu w.length
  have he (t : ι) : q t w = p t w :=
    (hq t w.length).eq_of_nil_eq (hp t) ((hq0 t).trans (hp0 t).symm) w le_rfl
  simpa only [he] using hpc w le_rfl

end PoincareConjecture.M35.Uniqueness.Heat
