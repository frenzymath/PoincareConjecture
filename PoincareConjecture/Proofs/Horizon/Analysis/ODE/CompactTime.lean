import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.Smooth

noncomputable section

namespace Poincare.ODE

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivWithinAt_glue
    {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {F : ℝ → E → E} {γ₁ γ₂ : ℝ → E}
    (h₁ : ∀ t ∈ Icc a c, HasDerivWithinAt γ₁ (F t (γ₁ t)) (Icc a c) t)
    (h₂ : ∀ t ∈ Icc c b, HasDerivWithinAt γ₂ (F t (γ₂ t)) (Icc c b) t)
    (hjoin : γ₂ c = γ₁ c) :
    ∀ t ∈ Icc a b, HasDerivWithinAt
      (fun s => if s ≤ c then γ₁ s else γ₂ s)
      (F t (if t ≤ c then γ₁ t else γ₂ t)) (Icc a b) t := by
  let γ : ℝ → E := fun t => if t ≤ c then γ₁ t else γ₂ t
  change ∀ t ∈ Icc a b, HasDerivWithinAt γ (F t (γ t)) (Icc a b) t
  intro t ht
  rcases lt_trichotomy t c with htc | he | hct
  · have hval : γ t = γ₁ t := if_pos htc.le
    have hset : (Icc a c : Set ℝ) =ᶠ[𝓝 t] Icc a b := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [isOpen_Iio.mem_nhds htc] with s hs
      exact ⟨fun h => ⟨h.1, h.2.trans hcb⟩, fun h => ⟨h.1, hs.le⟩⟩
    have heq : γ =ᶠ[𝓝[Icc a b] t] γ₁ := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds htc)] with s hs
      exact if_pos hs.le
    rw [hval]
    exact ((h₁ t ⟨ht.1, htc.le⟩).congr_set hset).congr_of_eventuallyEq heq hval
  · subst t
    have hval : γ c = γ₁ c := if_pos le_rfl
    have hleft : HasDerivWithinAt γ (F c (γ c)) (Icc a c) c := by
      rw [hval]
      exact (h₁ c ⟨hac, le_rfl⟩).congr (fun s hs => if_pos hs.2) hval
    have hright : HasDerivWithinAt γ (F c (γ c)) (Icc c b) c := by
      rw [hval, ← hjoin]
      refine (h₂ c ⟨le_rfl, hcb⟩).congr (fun s hs => ?_) (hval.trans hjoin.symm)
      by_cases hsc : s ≤ c
      · have he : s = c := le_antisymm hsc hs.1
        subst s
        exact hval.trans hjoin.symm
      · exact if_neg hsc
    simpa only [Icc_union_Icc_eq_Icc hac hcb] using hleft.union hright
  · have hval : γ t = γ₂ t := if_neg hct.not_ge
    have hset : (Icc c b : Set ℝ) =ᶠ[𝓝 t] Icc a b := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [isOpen_Ioi.mem_nhds hct] with s hs
      exact ⟨fun h => ⟨hac.trans h.1, h.2⟩, fun h => ⟨hs.le, h.2⟩⟩
    have heq : γ =ᶠ[𝓝[Icc a b] t] γ₂ := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hct)] with s hs
      exact if_neg hs.not_ge
    rw [hval]
    exact ((h₂ t ⟨hct.le, ht.2⟩).congr_set hset).congr_of_eventuallyEq heq hval

theorem exists_uniform_local_solutions [FiniteDimensional ℝ E]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {F : E → E} (hF : ContDiffOn ℝ ∞ F U) :
    ∃ δ > 0, ∀ x ∈ K, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-δ) δ, γ t ∈ U ∧ HasDerivAt γ (F (γ t)) t := by
  let P : Set E → Prop := fun S => ∃ δ > 0, ∀ x ∈ S, ∃ γ : ℝ → E, γ 0 = x ∧
    ∀ t ∈ Ioo (-δ) δ, γ t ∈ U ∧ HasDerivAt γ (F (γ t)) t
  change P K
  refine hK.induction_on (p := P) ?_ ?_ ?_ ?_
  · exact ⟨1, zero_lt_one, fun _ hx => False.elim hx⟩
  · rintro S T hST ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun x hx => h x (hST hx)⟩
  · rintro S T ⟨δ, hδ, hS⟩ ⟨ε, hε, hT⟩
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨γ, hinit, hγ⟩ := hS x hx
      exact ⟨γ, hinit, fun t ht => hγ t
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1,
          ht.2.trans_le (min_le_left _ _)⟩⟩
    · obtain ⟨γ, hinit, hγ⟩ := hT x hx
      exact ⟨γ, hinit, fun t ht => hγ t
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) ht.1,
          ht.2.trans_le (min_le_right _ _)⟩⟩
  · intro x hx
    obtain ⟨V, δ, Φ, hV, hxV, _, hδ, _, hinit, hmaps, hderiv⟩ :=
      LocalFlow.exists_smooth_localFlow hU hF (hKU hx)
    refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), δ, hδ, ?_⟩
    intro y hy
    exact ⟨fun t => Φ (y, t), hinit y hy, fun t ht =>
      ⟨hmaps y hy t ht, hderiv y hy t ht⟩⟩

end Poincare.ODE
