import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

theorem exists_common_negative_end_cut (C : BalancedNeckChain g ε)
    {i : ℤ} (hi : i ∈ C.shape.active) (J : Finset ℤ)
    (hJ : ∀ j ∈ J, j ∈ C.shape.active ∧ i < j)
    {b : ℝ} (hb : -ε⁻¹ < b) :
    ∃ a ∈ Ioo (-ε⁻¹) b, ∀ j ∈ J,
      Disjoint (C.neck j).carrier ((C.neck i).region (-ε⁻¹) a) := by
  induction J using Finset.induction_on with
  | empty =>
    obtain ⟨a, ha, hab⟩ := exists_between hb
    exact ⟨a, ⟨ha, hab⟩, by simp⟩
  | @insert j J hj ih =>
    obtain ⟨a, ha, havoid⟩ := ih (fun k hk => hJ k (Finset.mem_insert_of_mem hk))
    obtain ⟨s, hs, hdisj⟩ := C.later_disjoint_negative_end i hi j
      (hJ j (Finset.mem_insert_self _ _)).1 (hJ j (Finset.mem_insert_self _ _)).2
    refine ⟨min a s, ⟨lt_min ha.1 hs.1, (min_le_left _ _).trans_lt ha.2⟩, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · apply hdisj.mono_right
      intro x hx
      exact ⟨hx.1, hx.2.1, hx.2.2.trans_le (min_le_right _ _)⟩
    · apply (havoid k hk).mono_right
      intro x hx
      exact ⟨hx.1, hx.2.1, hx.2.2.trans_le (min_le_left _ _)⟩

end PoincareConjecture.BalancedNeckChain
