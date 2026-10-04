import PoincareLib.Geometry.RicciFlow.Generalized.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Generalized blowup sequences and normalized balls

Adapted from Mapher, `PoincareMT/Definitions/Ch11/BlowupLimits.lean`, commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Declaration bodies are retained; only the required definition closure is imported.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

structure GeneralizedBlowupSequence where
  flow : ℕ → GeneralizedRicciFlowData.{u}
  base : ∀ k, (flow k).point
  base_scalar_pos : ∀ k, 0 < (flow k).scalar (base k)
  scalar_diverges : Filter.Tendsto (fun k ↦ (flow k).scalar (base k))
    Filter.atTop Filter.atTop

noncomputable def GeneralizedBlowupSequence.scale (S : GeneralizedBlowupSequence)
    (k : ℕ) : ℝ := (S.flow k).scalar (S.base k)

def GeneralizedBlowupSequence.baseBall (S : GeneralizedBlowupSequence)
    (k : ℕ) (A : ℝ) : Set ((S.flow k).slice (S.base k).1).carrier :=
  ((S.flow k).metric (S.base k).1).ball (S.base k).2 (A / Real.sqrt (S.scale k))

def GeneralizedBlowupBoundedDistance (S : GeneralizedBlowupSequence) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in Filter.atTop,
    ∀ x ∈ S.baseBall k A,
      (S.flow k).scalar ⟨(S.base k).1, x⟩ ≤ D * S.scale k

end PoincareMT

