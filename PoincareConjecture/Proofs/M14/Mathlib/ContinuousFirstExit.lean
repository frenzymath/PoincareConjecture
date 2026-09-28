import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas











set_option autoImplicit false

open Set

namespace PoincareConjecture.M14




theorem exists_first_exit_of_continuousOn {X : Type*} [TopologicalSpace X]
    {γ : ℝ → X} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    {O : Set X} (hO : IsOpen O) (ha : γ a ∈ O)
    (hleave : ∃ s ∈ Icc a b, γ s ∉ O) :
    ∃ c ∈ Ioc a b, γ c ∉ O ∧ MapsTo γ (Ico a c) O ∧
      MapsTo γ (Icc a c) (closure O) := by
  let S := Icc a b ∩ γ ⁻¹' Oᶜ
  have hS : IsClosed S := hγ.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hnon : S.Nonempty := by
    obtain ⟨s, hs, hsO⟩ := hleave
    exact ⟨s, hs, hsO⟩
  have hbound : BddBelow S := ⟨a, fun _ hs => hs.1.1⟩
  obtain ⟨hc, hleast⟩ := hS.isLeast_csInf hnon hbound
  have hac : a < sInf S := lt_of_le_of_ne hc.1.1 (by
    intro h
    exact hc.2 (h ▸ ha))
  have hpre : MapsTo γ (Ico a (sInf S)) O := by
    intro s hs
    by_contra hnot
    exact (not_le_of_gt hs.2) (hleast ⟨⟨hs.1, hs.2.le.trans hc.1.2⟩, hnot⟩)
  have hcont : ContinuousOn γ (closure (Ico a (sInf S))) := by
    rw [closure_Ico hac.ne]
    exact hγ.mono (Icc_subset_Icc le_rfl hc.1.2)
  refine ⟨sInf S, ⟨hac, hc.1.2⟩, hc.2, hpre, ?_⟩
  have hcl := hpre.closure_of_continuousOn hcont
  rwa [closure_Ico hac.ne] at hcl

end PoincareConjecture.M14
