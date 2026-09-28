import Mathlib.Analysis.ODE.ExistUnique












set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareConjecture

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


def IsPicardIntervalSolution
    (f : ℝ → E → E) (tmin tmax : ℝ) (t₀ : Icc tmin tmax) (x₀ : E)
    (α : ℝ → E) : Prop :=
  α t₀ = x₀ ∧
    ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t


theorem exists_picardIntervalSolution
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E}
    {a L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, IsPicardIntervalSolution f tmin tmax t₀ x₀ α := by
  obtain ⟨α, hα₀, hα⟩ :=
    IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hf
  exact ⟨α, hα₀, hα⟩

end PoincareConjecture
