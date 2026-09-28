import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.SliceIdentifications







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture

theorem GeneralizedRicciFlowData.box_interval_subset
    (F : GeneralizedRicciFlowData.{u}) (b : F.box_index) :
    (F.box b).interval ⊆ F.interval := by
  obtain ⟨U, _, hU⟩ := (F.box b).relatively_open
  rw [hU]
  exact inter_subset_left

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem oldBox_time_ne_terminal (H : SingularTimeAssumptions F T M)
    (b : F.box_index) {t : ℝ} (ht : t ∈ (F.box b).interval) : t ≠ T := by
  intro h
  exact H.terminal_not_in_interval (h ▸ F.box_interval_subset b ht)

theorem oldBox_relatively_open (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (b : F.box_index) :
    ∃ U : Set ℝ, IsOpen U ∧
      (F.box b).interval = H.extendedTimeInterval P04 ∩ U := by
  obtain ⟨U, hU, heq⟩ := (F.box b).relatively_open
  refine ⟨U ∩ Iio T, hU.inter isOpen_Iio, ?_⟩
  ext t
  rw [heq]
  constructor
  · intro ht
    exact ⟨H.old_times_subset_extendedTimeInterval P04 ht.1, ht.2,
      (H.interval_preterminal ht.1).2⟩
  · rintro ⟨ht, hU, hT⟩
    refine ⟨?_, hU⟩
    rcases H.extendedTimeInterval_subset_old_union_terminal P04 ht with ht | ht
    · exact ht
    · exact (hT.ne ht).elim



def oldBox (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (b : F.box_index) :
    GeneralizedRicciFlowBox
      (fun t => (H.extendedSliceGeometry P04 t).slice)
      (fun t => (H.extendedSliceGeometry P04 t).metric)
      (H.extendedTimeInterval P04) where
  carrier := (F.box b).carrier
  interval := (F.box b).interval
  relatively_open := H.oldBox_relatively_open P04 b
  flow := (F.box b).flow
  forward := fun t ht =>
    H.oldSliceHomeomorph P04 (H.oldBox_time_ne_terminal b ht) ∘ (F.box b).forward t ht
  inverse := fun t ht =>
    (F.box b).inverse t ht ∘ (H.oldSliceHomeomorph P04 (H.oldBox_time_ne_terminal b ht)).symm
  forward_openEmbedding := fun t ht =>
    (H.oldSliceHomeomorph P04 (H.oldBox_time_ne_terminal b ht)).isOpenEmbedding.comp
      ((F.box b).forward_openEmbedding t ht)
  forward_smooth := fun t ht =>
    (H.oldSliceHomeomorph_smooth P04 (H.oldBox_time_ne_terminal b ht)).comp
      ((F.box b).forward_smooth t ht)
  inverse_smooth := by
    intro t ht
    apply ((F.box b).inverse_smooth t ht).comp
      (H.oldSliceHomeomorph_symm_smooth P04
        (H.oldBox_time_ne_terminal b ht)).contMDiffOn
    rintro z ⟨x, rfl⟩
    exact ⟨x, by simp only [Function.comp_apply, Homeomorph.symm_apply_apply]⟩
  left_inverse := by
    intro t ht x
    simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using
      (F.box b).left_inverse t ht x
  right_inverse := by
    intro t ht z hz
    rcases hz with ⟨x, rfl⟩
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply,
      (F.box b).left_inverse t ht x]
  metric_pullback := by
    intro t ht x v w
    rw [mfderiv_comp x
      ((H.oldSliceHomeomorph_smooth P04
        (H.oldBox_time_ne_terminal b ht)).mdifferentiable (by simp) _)
      (((F.box b).forward_smooth t ht).mdifferentiable (by simp) x)]
    exact (H.oldSliceHomeomorph_metric_pullback P04 (H.oldBox_time_ne_terminal b ht)
      ((F.box b).forward t ht x)
      (mfderiv (𝓡 3) (𝓡 3) ((F.box b).forward t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) ((F.box b).forward t ht) x w)).trans
        ((F.box b).metric_pullback t ht x v w)

@[simp] theorem oldBox_carrier (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (b : F.box_index) :
    (H.oldBox P04 b).carrier = (F.box b).carrier := rfl

@[simp] theorem oldBox_interval (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (b : F.box_index) :
    (H.oldBox P04 b).interval = (F.box b).interval := rfl

@[simp] theorem oldBox_flow (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (b : F.box_index) :
    (H.oldBox P04 b).flow = (F.box b).flow := rfl

theorem oldBox_forward (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (b : F.box_index)
    (t : ℝ) (ht : t ∈ (F.box b).interval) (x : (F.box b).carrier.carrier) :
    (H.oldBox P04 b).forward t ht x =
      H.oldSliceHomeomorph P04 (H.oldBox_time_ne_terminal b ht)
        ((F.box b).forward t ht x) := rfl

theorem oldBox_inverse (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (b : F.box_index)
    (t : ℝ) (ht : t ∈ (F.box b).interval)
    (x : (H.extendedSliceGeometry P04 t).slice.carrier) :
    (H.oldBox P04 b).inverse t ht x =
      (F.box b).inverse t ht
        ((H.oldSliceHomeomorph P04 (H.oldBox_time_ne_terminal b ht)).symm x) := rfl

end SingularTimeAssumptions

end PoincareConjecture
