import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.RegularSliceBuilder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

theorem m67_scalar_infimum_attained
    (F : RicciFlow 3 M (Set.Icc a b))
    (hcompact : IsCompact (Set.univ : Set M)) (x₀ : M)
    (t : Set.Icc a b) : ∃ x : M,
    (F.connection t.1).scalarCurvature x = flowScalarCurvatureInfimum F t.1 := by
  obtain ⟨x, _, hx⟩ := hcompact.exists_sInf_image_eq ⟨x₀, Set.mem_univ x₀⟩
    (F.contMDiff_scalarCurvature t.1 t.2).continuous.continuousOn
  exact ⟨x, by simpa [flowScalarCurvatureInfimum] using hx.symm⟩

theorem m67_scalar_infimum_continuous
    (F : RicciFlow 3 M (Set.Icc a b))
    (hcompact : IsCompact (Set.univ : Set M)) :
    Continuous (fun t : Set.Icc a b => flowScalarCurvatureInfimum F t.1) := by
  have hscalar : ContinuousOn (fun p : ℝ × M =>
      (F.connection p.1).scalarCurvature p.2) (Set.Icc a b ×ˢ Set.univ) :=
    F.contMDiffOn_scalarCurvature.continuousOn
  have hc : Continuous (fun p : Set.Icc a b × M =>
      (F.connection p.1.1).scalarCurvature p.2) :=
    hscalar.comp_continuous (f := fun p : Set.Icc a b × M => (p.1.1, p.2))
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.2, Set.mem_univ p.2⟩)
  change Continuous (fun t : Set.Icc a b =>
    sInf (Set.range (F.connection t.1).scalarCurvature))
  simpa only [Set.image_univ] using
    (hcompact.continuous_sInf (f := fun t : Set.Icc a b =>
      (F.connection t.1).scalarCurvature) hc)

noncomputable def m67RegularInputOfSlice
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    {q : M59SphereQuotient} (slice : M67WidthSlice q C)
    (hab : a < b) (F : RicciFlow 3 C.carrier.carrier (Set.Icc a b)) :
    M65RawFlowInput C.carrier.carrier a b where
  time_ordered := hab.le
  flow := F
  compact := C.compact
  hausdorff := inferInstance
  second_countable := inferInstance
  family := slice.family
  family_null := slice.family_null

theorem m67_regular_piece_of_actual_slice
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (S : M59IdentificationSystem.{u}) (slice : M67WidthSlice S.quotient C)
    {T : ℝ}
    (hM61 : M61RawWidthCore.{u}) {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61 hM58 hM65)
    (F : RicciFlow 3 C.carrier.carrier (Set.Icc a b))
    (width : Set.Icc (0 : ℝ) T → ℝ) (events : Set ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint events (Set.Ioc a b))
    (hwidth : ∀ s : Set.Icc a b,
      width ⟨s.1, ⟨ha.trans s.2.1, s.2.2.trans hb⟩⟩ =
        m66Width (m67RegularInputOfSlice C slice hab F) s) :
    Nonempty (M67RegularPiece hM61 hM65 F width events
      (a := a) (b := b) (T := T)) :=
  m67_regular_piece_of_slice C S slice hM61 hM65 hM58 hM66 F width events
    ha hab hb hJ (m67RegularInputOfSlice C slice hab F) rfl rfl
    (m67_scalar_infimum_attained F C.compact C.basepoint)
    (m67_scalar_infimum_continuous F C.compact) hwidth

end PoincareConjecture
