import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.M66ClassBuilder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.RegularPieceBuilder
import PoincareConjecture.Definitions.M67

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareConjecture

theorem m67_regular_piece_of_slice
    {A : GeneralizedSliceCarrier.{u}}
    (C : SurgerySelectedComponent A)
    (S : M59IdentificationSystem.{u})
    (slice : M67WidthSlice S.quotient C)
    {a b T : ℝ}
    (hM61 : M61RawWidthCore.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61 hM58 hM65)
    (actual_flow : RicciFlow 3 C.carrier.carrier (Set.Icc a b))
    (global_width : Set.Icc (0 : ℝ) T → ℝ)
    (events : Set ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint events (Set.Ioc a b))
    (input : M65RawFlowInput C.carrier.carrier a b)
    (hinput : input.flow = actual_flow)
    (hfamily : input.family = slice.family)
    (hscalar_infimum_attained : ∀ t : Set.Icc a b, ∃ x : C.carrier.carrier,
      (input.flow.connection t.1).scalarCurvature x =
        flowScalarCurvatureInfimum input.flow t.1)
    (hscalar_infimum_continuous : Continuous (fun t : Set.Icc a b =>
      flowScalarCurvatureInfimum input.flow t.1))
    (hwidth : ∀ s : Set.Icc a b,
      global_width ⟨s.1, ⟨ha.trans s.2.1, s.2.2.trans hb⟩⟩ = m66Width input s) :
    Nonempty (M67RegularPiece hM61 hM65 actual_flow global_width events
      (a := a) (b := b) (T := T)) := by
  have hrep : M61Represents S.quotient C.basepoint slice.alpha input.family := by
    rw [hfamily]
    exact slice.represents
  let class_data := m66ClassData_of_m59_representation input hab C.connected
    C.basepoint slice.pi_two_trivial
    S
    slice.alpha hrep slice.loop_pi_three slice.class_nonzero
    hscalar_infimum_attained hscalar_infimum_continuous
  exact m67_regular_piece_of_m66 hM61 hM65 hM58 hM66 actual_flow global_width
    events ha hab hb hJ input hinput class_data hwidth

end PoincareConjecture
