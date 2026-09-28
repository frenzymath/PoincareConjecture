import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic









set_option autoImplicit false

open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

theorem positive_everywhere_of_local_transfer
    {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    {a b : ℝ} (hab : a < b) (f : ℝ → M → ℝ)
    (hf : ∀ t ∈ Icc a b, Continuous (f t))
    (hlocal : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ s t : ℝ, a ≤ s → s < t → t ≤ b → ∀ y ∈ U, ∀ z ∈ U,
        0 < f s y → 0 < f t z)
    (p : M) (hp : 0 < f a p) : ∀ x : M, 0 < f b x := by
  let S : Set M := {x | ∃ t ∈ Ioo a b, 0 < f t x}
  have hSo : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨t, ht, htx⟩ := hx
    apply mem_of_superset ((isOpen_lt continuous_const (hf t ⟨ht.1.le, ht.2.le⟩)).mem_nhds htx)
    intro y hy
    exact ⟨t, ht, hy⟩
  have hSne : S.Nonempty := by
    obtain ⟨U, _, hpU, htransfer⟩ := hlocal p
    refine ⟨p, (a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    exact htransfer a ((a + b) / 2) le_rfl (by linarith) (by linarith) p hpU p hpU hp
  have hSc : IsClosed S := by
    apply isClosed_of_closure_subset
    intro x hx
    obtain ⟨U, hU, hxU, htransfer⟩ := hlocal x
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff_nhds.mp hx U (hU.mem_nhds hxU)
    obtain ⟨t, ht, hty⟩ := hyS
    refine ⟨(t + b) / 2, ⟨by linarith [ht.1, ht.2], by linarith [ht.2]⟩, ?_⟩
    exact htransfer t ((t + b) / 2) ht.1.le (by linarith [ht.2]) (by linarith [ht.2])
      y hyU x hxU hty
  have hSuniv : S = univ := (show IsClopen S from ⟨hSc, hSo⟩).eq_univ hSne
  intro x
  have hxS : x ∈ S := by rw [hSuniv]; exact mem_univ x
  obtain ⟨t, ht, htx⟩ := hxS
  obtain ⟨U, _, hxU, htransfer⟩ := hlocal x
  exact htransfer t b ht.1.le ht.2 le_rfl x hxU x hxU htx

end PoincareConjecture.RicciFlowAnalysis
