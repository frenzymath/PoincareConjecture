import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Scalar








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularRegularLimit


structure SliceGeometry where
  slice : GeneralizedSliceCarrier.{u}
  metric : RiemannianMetric 3 slice.carrier
  connection : LeviCivitaData metric

def SliceGeometry.ofFlow (F : GeneralizedRicciFlowData.{u}) (t : ℝ) : SliceGeometry.{u} :=
  ⟨F.slice t, F.metric t, F.connection t⟩

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


def terminalSliceCarrier (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : GeneralizedSliceCarrier.{u} where
  carrier := H.regularRegion P04
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

def terminalSliceGeometry (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : SingularRegularLimit.SliceGeometry.{u} :=
  ⟨H.terminalSliceCarrier P04, H.terminalMetric P04, H.terminalConnection P04⟩


def extendedSliceGeometry (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) : SingularRegularLimit.SliceGeometry.{u} :=
  if t = T then H.terminalSliceGeometry P04 else SingularRegularLimit.SliceGeometry.ofFlow F t

@[simp] theorem extendedSliceGeometry_terminal
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    H.extendedSliceGeometry P04 T = H.terminalSliceGeometry P04 := by
  simp [extendedSliceGeometry]

theorem extendedSliceGeometry_of_ne
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ≠ T) :
    H.extendedSliceGeometry P04 t = SingularRegularLimit.SliceGeometry.ofFlow F t := by
  simp only [extendedSliceGeometry, if_neg ht]


def extendedTimeInterval (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : Set ℝ := by
  classical
  exact if H.reference.regularLimitSet.Nonempty then Icc 0 T else F.interval

theorem extendedTimeInterval_connected
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    (H.extendedTimeInterval P04).OrdConnected := by
  unfold extendedTimeInterval
  split_ifs
  · exact ordConnected_Icc
  · exact F.interval_connected

theorem old_times_subset_extendedTimeInterval
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    F.interval ⊆ H.extendedTimeInterval P04 := by
  unfold extendedTimeInterval
  split_ifs
  · exact H.interval_preterminal.trans Ico_subset_Icc_self
  · exact subset_rfl

theorem extendedTimeInterval_subset_old_union_terminal
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    H.extendedTimeInterval P04 ⊆ F.interval ∪ {T} := by
  unfold extendedTimeInterval
  split_ifs
  · intro t ht
    rcases ht.2.eq_or_lt with h | h
    · exact Or.inr h
    · exact Or.inl (H.interval_exhausts_preterminal ⟨ht.1, h⟩)
  · exact subset_union_left

theorem extendedTimeInterval_nontrivial
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    (H.extendedTimeInterval P04).Nontrivial :=
  F.interval_nontrivial.mono (H.old_times_subset_extendedTimeInterval P04)

theorem terminal_mem_extendedTimeInterval_iff
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    T ∈ H.extendedTimeInterval P04 ↔ H.reference.regularLimitSet.Nonempty := by
  have hT : 0 < T :=
    (H.interval_nonnegative H.reference.tMinus_mem).trans_lt H.reference.tMinus_lt
  simp only [extendedTimeInterval]
  split_ifs with h
  · simp only [h, iff_true]
    exact ⟨hT.le, le_rfl⟩
  · simp only [h, iff_false]
    exact H.terminal_not_in_interval

theorem extendedSliceGeometry_nonempty_iff
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) :
    Nonempty (H.extendedSliceGeometry P04 t).slice.carrier ↔ t ∈ H.extendedTimeInterval P04 := by
  classical
  by_cases ht : t = T
  · subst t
    rw [H.extendedSliceGeometry_terminal P04, H.terminal_mem_extendedTimeInterval_iff P04]
    exact nonempty_subtype
  · rw [H.extendedSliceGeometry_of_ne P04 ht]
    change Nonempty (F.slice t).carrier ↔ _
    rw [F.slice_nonempty_iff]
    constructor
    · exact fun h => H.old_times_subset_extendedTimeInterval P04 h
    · intro h
      rcases H.extendedTimeInterval_subset_old_union_terminal P04 h with h | h
      · exact h
      · exact (ht h).elim

end PoincareConjecture.SingularTimeAssumptions
