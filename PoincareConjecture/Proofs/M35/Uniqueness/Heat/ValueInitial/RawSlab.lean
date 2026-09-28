import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.RawUniformRestart
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.FiniteContinuation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_raw_compact_vector_heat_on_slab {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) (hηK : ∀ x ∈ K, η x = 1)
    (u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K)) :
    ∃ v U, PrincipalValueHeat K
      (fun t => rawCutoffPrincipalCoefficient (F.metric t) η hη)
      (fun t => rawLowerFormOperator (F.connection t) hK.isClosed η hη) a (b - a) u₀ v U := by
  obtain ⟨τ, hτ, _, hsolve⟩ := exists_raw_uniform_value_restart F hJ hK η hη hη1 hηK
  exact exists_principal_value_heat_of_uniform_restart K
    (fun t => rawCutoffPrincipalCoefficient (F.metric t) η hη)
    (fun t => rawLowerFormOperator (F.connection t) hK.isClosed η hη) hab hτ
    (continuousOn_raw_principalFormOperator F isCompact_Icc hJ K η hη hη1)
    (continuousOn_rawLowerFormOperator F isCompact_Icc hJ hK.isClosed η hη hη1) hsolve u₀

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
