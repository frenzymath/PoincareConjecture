import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.SliceIdentifications
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Maps







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u v

noncomputable section

namespace PoincareConjecture.SingularRegularLimit


def openRetraction {X : Type u} [TopologicalSpace X]
    (U : Opens X) (x₀ : U) (x : X) : U := by
  classical
  exact if hx : x ∈ U then ⟨x, hx⟩ else x₀

@[simp] theorem openRetraction_coe {X : Type u} [TopologicalSpace X]
    (U : Opens X) (x₀ x : U) : openRetraction U x₀ (x : X) = x := by
  simp only [openRetraction, dif_pos x.property]

theorem openRetraction_val {X : Type u} [TopologicalSpace X]
    (U : Opens X) (x₀ : U) {x : X} (hx : x ∈ U) :
    (openRetraction U x₀ x : X) = x := by
  simp only [openRetraction, dif_pos hx]

theorem contMDiffOn_openRetraction_comp
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
    [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]
    (U : Opens Y) (x₀ : U) {f : X → Y} {S : Set X}
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f S) (hS : MapsTo f S U) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (openRetraction U x₀ ∘ f) S := by
  intro x hx
  rw [← ContMDiffWithinAt.subtypeVal_comp_iff U]
  exact (hf x hx).congr_of_mem
    (fun y hy => openRetraction_val U x₀ (hS hy)) hx

theorem SliceGeometry.homeomorphOfEq_symm_metric_pullback
    {G K : SliceGeometry.{u}} (h : G = K) (x : K.slice.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    G.metric.inner ((SliceGeometry.homeomorphOfEq h).symm x)
      (mfderiv (𝓡 3) (𝓡 3) (SliceGeometry.homeomorphOfEq h).symm x v)
      (mfderiv (𝓡 3) (𝓡 3) (SliceGeometry.homeomorphOfEq h).symm x w) =
        K.metric.inner x v w := by
  subst K
  change G.metric.inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
    (mfderiv (𝓡 3) (𝓡 3) id x w) = _
  rw [mfderiv_id]
  rfl

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.SingularTimeAssumptions

open SingularRegularLimit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

def regularBoxForward (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) :
    H.regularRegion P04 → (H.extendedSliceGeometry P04 t).slice.carrier := by
  by_cases hT : t = T
  · subst t
    exact fun x => (H.terminalSliceHomeomorph P04).symm x
  · exact H.oldSliceHomeomorph P04 hT ∘
      (H.reference.forward t ⟨ht.1.le, lt_of_le_of_ne ht.2 hT⟩ ∘ Subtype.val)

@[simp] theorem regularBoxForward_terminal (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (ht : T ∈ Ioc H.reference.tMinus T) :
    H.regularBoxForward P04 T ht = (H.terminalSliceHomeomorph P04).symm := by
  simp [regularBoxForward]

theorem regularBoxForward_of_lt (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T)
    (hlt : t < T) :
    H.regularBoxForward P04 t ht = H.oldSliceHomeomorph P04 hlt.ne ∘
      (H.reference.forward t ⟨ht.1.le, hlt⟩ ∘ Subtype.val) := by
  simp only [regularBoxForward, dif_neg hlt.ne]

def regularBoxInverse (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x₀ : H.regularRegion P04)
    (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) :
    (H.extendedSliceGeometry P04 t).slice.carrier → H.regularRegion P04 := by
  by_cases hT : t = T
  · subst t
    exact fun x => H.terminalSliceHomeomorph P04 x
  · exact openRetraction (H.regularRegion P04) x₀ ∘
      (H.reference.inverse t ⟨ht.1.le, lt_of_le_of_ne ht.2 hT⟩ ∘
        (H.oldSliceHomeomorph P04 hT).symm)

@[simp] theorem regularBoxInverse_terminal (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x₀ : H.regularRegion P04)
    (ht : T ∈ Ioc H.reference.tMinus T) :
    H.regularBoxInverse P04 x₀ T ht = H.terminalSliceHomeomorph P04 := by
  simp [regularBoxInverse]

theorem regularBoxInverse_of_lt (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x₀ : H.regularRegion P04)
    (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) (hlt : t < T) :
    H.regularBoxInverse P04 x₀ t ht = openRetraction (H.regularRegion P04) x₀ ∘
      (H.reference.inverse t ⟨ht.1.le, hlt⟩ ∘
        (H.oldSliceHomeomorph P04 hlt.ne).symm) := by
  simp only [regularBoxInverse, dif_neg hlt.ne]

theorem regularBoxForward_openEmbedding (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) :
    Topology.IsOpenEmbedding (H.regularBoxForward P04 t ht) := by
  rcases ht.2.eq_or_lt with hT | hlt
  · subst t
    rw [H.regularBoxForward_terminal P04]
    exact (H.terminalSliceHomeomorph P04).symm.isOpenEmbedding
  · rw [H.regularBoxForward_of_lt P04 t ht hlt]
    exact (H.oldSliceHomeomorph P04 hlt.ne).isOpenEmbedding.comp
      ((H.reference.forward_openEmbedding t ⟨ht.1.le, hlt⟩).comp
        (H.regularRegion P04).isOpen.isOpenEmbedding_subtypeVal)

theorem regularBoxForward_smooth (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (H.regularBoxForward P04 t ht) := by
  rcases ht.2.eq_or_lt with hT | hlt
  · subst t
    rw [H.regularBoxForward_terminal P04]
    exact H.terminalSliceHomeomorph_symm_smooth P04
  · rw [H.regularBoxForward_of_lt P04 t ht hlt]
    exact (H.oldSliceHomeomorph_smooth P04 hlt.ne).comp
      ((H.reference.forward_smooth t ⟨ht.1.le, hlt⟩).comp contMDiff_subtype_val)

theorem regularBox_left_inverse (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x₀ : H.regularRegion P04)
    (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) :
    Function.LeftInverse (H.regularBoxInverse P04 x₀ t ht) (H.regularBoxForward P04 t ht) := by
  rcases ht.2.eq_or_lt with hT | hlt
  · subst t
    rw [H.regularBoxForward_terminal P04, H.regularBoxInverse_terminal P04]
    exact (H.terminalSliceHomeomorph P04).apply_symm_apply
  · rw [H.regularBoxForward_of_lt P04 t ht hlt, H.regularBoxInverse_of_lt P04 x₀ t ht hlt]
    intro x
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply,
      H.reference.left_inverse t ⟨ht.1.le, hlt⟩ (x : M), openRetraction_coe]

theorem regularBoxInverse_smooth (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x₀ : H.regularRegion P04)
    (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (H.regularBoxInverse P04 x₀ t ht)
      (range (H.regularBoxForward P04 t ht)) := by
  rcases ht.2.eq_or_lt with hT | hlt
  · subst t
    rw [H.regularBoxInverse_terminal P04]
    exact (H.terminalSliceHomeomorph_smooth P04).contMDiffOn
  · rw [H.regularBoxForward_of_lt P04 t ht hlt, H.regularBoxInverse_of_lt P04 x₀ t ht hlt]
    apply contMDiffOn_openRetraction_comp
      (hf := ((H.reference.inverse_smooth t ⟨ht.1.le, hlt⟩).comp
        (H.oldSliceHomeomorph_symm_smooth P04 hlt.ne)).contMDiffOn)
    rintro z ⟨x, rfl⟩
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply,
      H.reference.left_inverse t ⟨ht.1.le, hlt⟩ (x : M)]
    exact x.property

theorem regularBox_metric_pullback (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T)
    (x : H.regularRegion P04) (v w : TangentSpace (𝓡 3) x) :
    (H.extendedSliceGeometry P04 t).metric.inner (H.regularBoxForward P04 t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (H.regularBoxForward P04 t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (H.regularBoxForward P04 t ht) x w) =
        ((H.terminalFlow P04).metric t).inner x v w := by
  rcases ht.2.eq_or_lt with hT | hlt
  · subst t
    rw [H.regularBoxForward_terminal P04, H.terminalFlow_metric_at_terminal P04]
    exact SliceGeometry.homeomorphOfEq_symm_metric_pullback
      (G := H.extendedSliceGeometry P04 T) (K := H.terminalSliceGeometry P04)
      (H.extendedSliceGeometry_terminal P04) x v w
  · rw [H.regularBoxForward_of_lt P04 t ht hlt, H.terminalFlow_metric_of_lt P04 hlt]
    let r := H.reference.forward t ⟨ht.1.le, hlt⟩
    let i := (Subtype.val : H.regularRegion P04 → M)
    have hr := H.reference.forward_smooth t ⟨ht.1.le, hlt⟩
    have hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i := contMDiff_subtype_val
    have hcomp := (hr.comp hi).mdifferentiable (by simp) x
    rw [mfderiv_comp x ((H.oldSliceHomeomorph_smooth P04 hlt.ne).mdifferentiable
      (by simp) _) hcomp]
    refine (H.oldSliceHomeomorph_metric_pullback P04 hlt.ne ((r ∘ i) x)
      (mfderiv (𝓡 3) (𝓡 3) (r ∘ i) x v)
      (mfderiv (𝓡 3) (𝓡 3) (r ∘ i) x w)).trans ?_
    rw [mfderiv_comp x (hr.mdifferentiable (by simp) _) (hi.mdifferentiable (by simp) x)]
    exact H.reference.metric_pullback t ⟨ht.1.le, hlt⟩ x
      (mfderiv (𝓡 3) (𝓡 3) i x v) (mfderiv (𝓡 3) (𝓡 3) i x w)

theorem regularBox_relatively_open (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty) :
    ∃ U : Set ℝ, IsOpen U ∧ Ioc H.reference.tMinus T = H.extendedTimeInterval P04 ∩ U := by
  refine ⟨Ioi H.reference.tMinus, isOpen_Ioi, ?_⟩
  ext t
  simp only [extendedTimeInterval, if_pos hΩ, mem_Ioc, mem_inter_iff, mem_Icc, mem_Ioi]
  constructor
  · intro ht
    exact ⟨⟨(H.interval_nonnegative H.reference.tMinus_mem).trans ht.1.le, ht.2⟩, ht.1⟩
  · intro ht
    exact ⟨ht.2, ht.1.2⟩


def regularBox (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty) :
    GeneralizedRicciFlowBox
      (fun t => (H.extendedSliceGeometry P04 t).slice)
      (fun t => (H.extendedSliceGeometry P04 t).metric)
      (H.extendedTimeInterval P04) where
  carrier := H.terminalSliceCarrier P04
  interval := Ioc H.reference.tMinus T
  relatively_open := H.regularBox_relatively_open P04 hΩ
  flow := H.terminalFlow P04
  forward := H.regularBoxForward P04
  inverse := H.regularBoxInverse P04 ⟨hΩ.choose, hΩ.choose_spec⟩
  forward_openEmbedding := H.regularBoxForward_openEmbedding P04
  forward_smooth := H.regularBoxForward_smooth P04
  inverse_smooth := H.regularBoxInverse_smooth P04 _
  left_inverse := H.regularBox_left_inverse P04 _
  right_inverse := by
    intro t ht z hz
    rcases hz with ⟨x, rfl⟩
    rw [H.regularBox_left_inverse P04 _ t ht x]
  metric_pullback := H.regularBox_metric_pullback P04

@[simp] theorem regularBox_forward_terminal (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty)
    (ht : T ∈ Ioc H.reference.tMinus T) (x : H.regularRegion P04) :
    (H.regularBox P04 hΩ).forward T ht x = (H.terminalSliceHomeomorph P04).symm x := by
  exact congrFun (H.regularBoxForward_terminal P04 ht) x

theorem regularBox_forward_old (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty)
    (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) (hlt : t < T)
    (x : H.regularRegion P04) :
    (H.regularBox P04 hΩ).forward t ht x = H.oldSliceHomeomorph P04 hlt.ne
      (H.reference.forward t ⟨ht.1.le, hlt⟩ x) := by
  exact congrFun (H.regularBoxForward_of_lt P04 t ht hlt) x

theorem regularBox_spacetime_forward (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty)
    (p : Ioc H.reference.tMinus T × H.regularRegion P04) :
    (⟨p.1, (H.regularBox P04 hΩ).forward p.1 p.1.property p.2⟩ : H.extendedPoint P04) =
      H.regularSpacetimeForward P04 p := by
  rcases p with ⟨⟨t, ht⟩, x⟩
  rcases ht.2.eq_or_lt with hT | hlt
  · subst t
    rw [H.regularBox_forward_terminal P04, H.regularSpacetimeForward_terminal P04]
  · rw [H.regularBox_forward_old P04 hΩ t ht hlt,
      H.regularSpacetimeForward_old P04 t ht hlt, H.oldSpacetimeForward_eq P04 hlt.ne]

theorem regularBox_spacetime_forward_eq (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty)
    (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T) (x : H.regularRegion P04) :
    (⟨t, (H.regularBox P04 hΩ).forward t ht x⟩ : H.extendedPoint P04) =
      H.regularSpacetimeForward P04 (⟨t, ht⟩, x) :=
  H.regularBox_spacetime_forward P04 hΩ (⟨t, ht⟩, x)

end PoincareConjecture.SingularTimeAssumptions
