import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Uniqueness.Open

open Set
open scoped ContDiff

namespace Poincare.ODE

theorem eqOn_Icc_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} (hF : ContDiff ℝ 1 F) {γ η : ℝ → E} {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (F (γ t)) t)
    (hη : ∀ t ∈ Icc a b, HasDerivAt η (F (η t)) t)
    (heq : γ a = η a) : EqOn γ η (Icc a b) := by
  have hcγ : ContinuousOn γ (Icc a b) :=
    fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hcη : ContinuousOn η (Icc a b) :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  let K := γ '' Icc a b ∪ η '' Icc a b
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hcγ).union
    (isCompact_Icc.image_of_continuousOn hcη)
  obtain ⟨C, hC⟩ := hF.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => K)
    (fun _ _ => hC) hcγ
    (fun t ht => (hγ t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩) hcη
    (fun t ht => (hη t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) heq

end Poincare.ODE
