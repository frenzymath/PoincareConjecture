import PoincareConjecture.Statements.M67

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareConjecture

theorem m67_regular_piece_of_m66
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b T : ℝ}
    (hM61 : M61RawWidthCore.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61 hM58 hM65)
    (actual_flow : RicciFlow 3 M (Set.Icc a b))
    (global_width : Set.Icc (0 : ℝ) T → ℝ)
    (events : Set ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint events (Set.Ioc a b))
    (input : M65RawFlowInput M a b)
    (hinput : input.flow = actual_flow)
    (class_data : M66ClassData input)
    (hwidth : ∀ s : Set.Icc a b,
      global_width ⟨s.1, ⟨ha.trans s.2.1, s.2.2.trans hb⟩⟩ = m66Width input s) :
    Nonempty (M67RegularPiece hM61 hM65 actual_flow global_width events
      (a := a) (b := b) (T := T)) := by
  let predecessors := m66PredecessorsFromServices hM61 hM58 hM65 input class_data
  obtain ⟨conclusion⟩ := hM66 M input class_data
  refine ⟨{
    ordered := hab
    inside := ⟨ha, hb⟩
    no_event := hJ
    input := input
    input_flow_eq := hinput
    class_data := class_data
    predecessors := predecessors
    conclusion := conclusion
    interval := fun s => ⟨s.1, ⟨ha.trans s.2.1, s.2.2.trans hb⟩⟩
    interval_time := fun s => rfl
    width_agreement := hwidth }⟩

end PoincareConjecture
