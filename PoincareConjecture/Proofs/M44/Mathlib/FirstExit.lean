import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas










set_option autoImplicit false

open Set



theorem ContinuousOn.exists_first_frontier_time
    {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    {U : Set X} (hU : IsOpen U) (ha : γ a ∈ U) (hb : γ b ∉ U) :
    ∃ c ∈ Ioc a b, γ c ∈ frontier U ∧
      MapsTo γ (Ico a c) U ∧ MapsTo γ (Icc a c) (closure U) := by
  let S : Set ℝ := Icc a b ∩ γ ⁻¹' Uᶜ
  have hS : IsClosed S :=
    hγ.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl
  have hSne : S.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  have hSb : BddBelow S := ⟨a, fun _ hs => hs.1.1⟩
  let c := sInf S
  have hc : c ∈ S := hS.csInf_mem hSne hSb
  have hac : a < c := lt_of_le_of_ne hc.1.1 (by
    intro heq
    exact hc.2 (heq ▸ ha))
  have hprior : MapsTo γ (Ico a c) U := by
    intro s hs
    by_contra hnot
    have hsS : s ∈ S := ⟨⟨hs.1, hs.2.le.trans hc.1.2⟩, hnot⟩
    exact (not_le_of_gt hs.2) (csInf_le hSb hsS)
  have hccl : c ∈ closure (Ico a c) := by
    rw [closure_Ico hac.ne]
    exact ⟨hac.le, le_rfl⟩
  have hcl : γ c ∈ closure U :=
    ((hγ c hc.1).mono (Ico_subset_Icc_self.trans
      (Icc_subset_Icc le_rfl hc.1.2))).mem_closure hccl hprior
  refine ⟨c, ⟨hac, hc.1.2⟩, ?_, hprior, ?_⟩
  · rw [frontier, hU.interior_eq]
    exact ⟨hcl, hc.2⟩
  · intro s hs
    rcases lt_or_eq_of_le hs.2 with hsc | rfl
    · exact subset_closure (hprior ⟨hs.1, hsc⟩)
    · exact hcl




theorem ContinuousOn.mapsTo_of_open_prefix
    {X : Type*} [TopologicalSpace X] {f : ℝ → X} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {U : Set X} (hU : IsOpen U) (ha : f a ∈ U)
    (hstep : ∀ c ∈ Ioc a b, MapsTo f (Ico a c) U → f c ∈ U) :
    MapsTo f (Icc a b) U := by
  intro t ht
  by_contra hnot
  obtain ⟨c, hc, hfront, hprior, _hclosed⟩ :=
    (hf.mono (Icc_subset_Icc le_rfl ht.2)).exists_first_frontier_time ht.1 hU ha hnot
  rw [frontier, hU.interior_eq] at hfront
  exact hfront.2 (hstep c ⟨hc.1, hc.2.trans ht.2⟩ hprior)
