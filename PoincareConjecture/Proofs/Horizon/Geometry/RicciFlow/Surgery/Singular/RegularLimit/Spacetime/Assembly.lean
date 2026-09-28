import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.RegularBox
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.GluingTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Worldlines








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

def extendedBox (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty)
    (b : F.box_index ⊕ PUnit.{u + 1}) :
    GeneralizedRicciFlowBox
      (fun t => (H.extendedSliceGeometry P04 t).slice)
      (fun t => (H.extendedSliceGeometry P04 t).metric)
      (H.extendedTimeInterval P04) :=
  match b with
  | .inl b => H.oldBox P04 b
  | .inr _ => H.regularBox P04 hΩ

theorem oldBox_spacetime_forward (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (b : F.box_index)
    (p : (F.box b).interval × (F.box b).carrier.carrier) :
    (⟨p.1, (H.oldBox P04 b).forward p.1 p.1.property p.2⟩ : H.extendedPoint P04) =
      H.oldSpacetimeForward P04 ⟨p.1, (F.box b).forward p.1 p.1.property p.2⟩ := rfl

theorem extendedBox_openEmbedding (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty)
    (b : F.box_index ⊕ PUnit.{u + 1}) :
    letI := H.extendedSpacetimeTopology P04
    Topology.IsOpenEmbedding (fun p : (H.extendedBox P04 hΩ b).interval ×
      (H.extendedBox P04 hΩ b).carrier.carrier =>
        (⟨p.1, (H.extendedBox P04 hΩ b).forward p.1 p.1.property p.2⟩ :
          H.extendedPoint P04)) := by
  let := H.extendedSpacetimeTopology P04
  cases b with
  | inl b =>
      exact (H.oldSpacetimeForward_isOpenEmbedding P04).comp (F.box_openEmbedding b)
  | inr b =>
      have heq : (fun p : Ioc H.reference.tMinus T × H.regularRegion P04 =>
          (⟨p.1, (H.regularBox P04 hΩ).forward p.1 p.1.property p.2⟩ :
            H.extendedPoint P04)) = H.regularSpacetimeForward P04 :=
        funext (H.regularBox_spacetime_forward P04 hΩ)
      change Topology.IsOpenEmbedding (fun p : Ioc H.reference.tMinus T ×
        H.regularRegion P04 =>
          (⟨p.1, (H.regularBox P04 hΩ).forward p.1 p.1.property p.2⟩ :
            H.extendedPoint P04))
      rw [heq]
      exact H.regularSpacetimeForward_isOpenEmbedding P04

theorem extendedBox_covers (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty)
    (t : ℝ) (x : (H.extendedSliceGeometry P04 t).slice.carrier) :
    ∃ b, ∃ ht : t ∈ (H.extendedBox P04 hΩ b).interval,
      ∃ y, (H.extendedBox P04 hΩ b).forward t ht y = x := by
  by_cases ht : t = T
  · subst t
    refine ⟨.inr PUnit.unit, ⟨H.reference.tMinus_lt, le_rfl⟩,
      H.terminalSliceHomeomorph P04 x, ?_⟩
    change (H.regularBox P04 hΩ).forward T _ (H.terminalSliceHomeomorph P04 x) = x
    rw [H.regularBox_forward_terminal P04]
    exact (H.terminalSliceHomeomorph P04).symm_apply_apply x
  · obtain ⟨b, hb, y, hy⟩ := F.box_covers t ((H.oldSliceHomeomorph P04 ht).symm x)
    refine ⟨.inl b, hb, y, ?_⟩
    change H.oldSliceHomeomorph P04 ht ((F.box b).forward t hb y) = x
    rw [hy, Homeomorph.apply_symm_apply]

theorem old_regular_box_vertical_compatibility
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hΩ : H.reference.regularLimitSet.Nonempty) (b : F.box_index)
    (t : ℝ) (ht : t ∈ (F.box b).interval) (hc : t ∈ Ioc H.reference.tMinus T)
    (x : (F.box b).carrier.carrier) (y : H.regularRegion P04)
    (heq : (H.oldBox P04 b).forward t ht x = (H.regularBox P04 hΩ).forward t hc y)
    (s : ℝ) (hs : s ∈ (F.box b).interval) (hs' : s ∈ Ioc H.reference.tMinus T) :
    (H.oldBox P04 b).forward s hs x = (H.regularBox P04 hΩ).forward s hs' y := by
  have hsig := congrArg (fun z : (H.extendedSliceGeometry P04 t).slice.carrier =>
    (⟨t, z⟩ : H.extendedPoint P04)) heq
  change (⟨t, (H.oldBox P04 b).forward t ht x⟩ : H.extendedPoint P04) = _ at hsig
  rw [H.oldBox_spacetime_forward P04 b (⟨t, ht⟩, x),
    H.regularBox_spacetime_forward P04 hΩ (⟨t, hc⟩, y)] at hsig
  have hnew := H.regularSpacetimeForward_eq_oldBox_of_eq P04 b x y hc ht hsig.symm hs' hs
  rw [← H.oldBox_spacetime_forward P04 b (⟨s, hs⟩, x),
    ← H.regularBox_spacetime_forward P04 hΩ (⟨s, hs'⟩, y)] at hnew
  exact (eq_of_heq (Sigma.mk.inj_iff.mp hnew).2).symm

theorem extendedBox_vertical_compatibility
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hΩ : H.reference.regularLimitSet.Nonempty) (b c : F.box_index ⊕ PUnit.{u + 1})
    (t : ℝ) (ht : t ∈ (H.extendedBox P04 hΩ b).interval)
    (hc : t ∈ (H.extendedBox P04 hΩ c).interval)
    (x : (H.extendedBox P04 hΩ b).carrier.carrier)
    (y : (H.extendedBox P04 hΩ c).carrier.carrier)
    (heq : (H.extendedBox P04 hΩ b).forward t ht x =
      (H.extendedBox P04 hΩ c).forward t hc y)
    (s : ℝ) (hs : s ∈ (H.extendedBox P04 hΩ b).interval)
    (hs' : s ∈ (H.extendedBox P04 hΩ c).interval) :
    (H.extendedBox P04 hΩ b).forward s hs x =
      (H.extendedBox P04 hΩ c).forward s hs' y := by
  cases b with
  | inl b =>
      cases c with
      | inl c =>
          have hbase := (H.oldSliceHomeomorph P04 (H.oldBox_time_ne_terminal b ht)).injective heq
          exact congrArg (H.oldSliceHomeomorph P04 (H.oldBox_time_ne_terminal b hs))
            (F.vertical_compatibility b c t ht hc x y hbase s hs hs')
      | inr c => exact H.old_regular_box_vertical_compatibility P04 hΩ b t ht hc x y heq s hs hs'
  | inr b =>
      cases c with
      | inl c =>
          exact (H.old_regular_box_vertical_compatibility P04 hΩ c t hc ht y x heq.symm s hs' hs).symm
      | inr c =>
          have hxy := ((H.regularBox P04 hΩ).forward_openEmbedding t ht).injective heq
          exact congrArg ((H.regularBox P04 hΩ).forward s hs) hxy



def nonemptyExtendedFlow (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty) :
    GeneralizedRicciFlowData.{u} where
  slice t := (H.extendedSliceGeometry P04 t).slice
  interval := H.extendedTimeInterval P04
  interval_connected := H.extendedTimeInterval_connected P04
  interval_nontrivial := H.extendedTimeInterval_nontrivial P04
  slice_nonempty_iff := H.extendedSliceGeometry_nonempty_iff P04
  metric t := (H.extendedSliceGeometry P04 t).metric
  connection t := (H.extendedSliceGeometry P04 t).connection
  space_topology := H.extendedSpacetimeTopology P04
  space_t2 := H.extendedSpacetime_t2 P04
  space_secondCountable := H.extendedSpacetime_secondCountable P04
  time_continuous := H.extendedSpacetime_time_continuous P04
  slice_embedding := H.extendedSpacetime_slice_embedding P04
  box_index := F.box_index ⊕ PUnit.{u + 1}
  box := H.extendedBox P04 hΩ
  box_openEmbedding := H.extendedBox_openEmbedding P04 hΩ
  box_covers := H.extendedBox_covers P04 hΩ
  vertical_compatibility := H.extendedBox_vertical_compatibility P04 hΩ


def nonemptyExtension (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty) :
    GeneralizedFlowExtension F T where
  extended := H.nonemptyExtendedFlow P04 hΩ
  times_subset := H.extendedTimeInterval_subset_old_union_terminal P04
  old_times := H.old_times_subset_extendedTimeInterval P04
  forward t ht := H.oldSliceHomeomorph P04 (fun heq => H.terminal_not_in_interval (heq ▸ ht))
  inverse t ht := (H.oldSliceHomeomorph P04 (fun heq => H.terminal_not_in_interval (heq ▸ ht))).symm
  forward_smooth t ht := H.oldSliceHomeomorph_smooth P04 _
  inverse_smooth t ht := H.oldSliceHomeomorph_symm_smooth P04 _
  left_inverse t ht := (H.oldSliceHomeomorph P04 _).symm_apply_apply
  right_inverse t ht := (H.oldSliceHomeomorph P04 _).apply_symm_apply
  metric_pullback t ht := H.oldSliceHomeomorph_metric_pullback P04 _
  scalar_pullback t ht := H.oldSliceHomeomorph_scalar_pullback P04 _
  spacetime_forward := H.oldSpacetimeForward P04
  spacetime_time := H.oldSpacetimeForward_time P04
  spacetime_slices t ht x := rfl
  spacetime_openEmbedding := H.oldSpacetimeForward_isOpenEmbedding P04
  spacetime_image := H.oldSpacetimeForward_range P04
  vertical_compatibility b t ht x := by
    refine ⟨.inl b, x, 1, by norm_num, ?_⟩
    intro s hs _
    exact ⟨hs, rfl⟩

end PoincareConjecture.SingularTimeAssumptions
