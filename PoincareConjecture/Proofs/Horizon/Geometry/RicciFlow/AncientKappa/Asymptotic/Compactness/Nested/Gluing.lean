import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Family







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

noncomputable def selectedCompactnessWindow (t : ℝ) : ℕ :=
  if ht : t < 1 then Classical.choose (exists_mem_shiftedCompactnessWindow t ht) else 0

theorem selectedCompactnessWindow_mem {t : ℝ} (ht : t < 1) :
    t ∈ shiftedCompactnessWindow (selectedCompactnessWindow t) := by
  simpa only [selectedCompactnessWindow, dif_pos ht] using
    Classical.choose_spec (exists_mem_shiftedCompactnessWindow t ht)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

noncomputable def selectedWindowMetric (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (t : ℝ) :
    RiemannianMetric n (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier :=
  (S.identifiedWindowFlow P (selectedCompactnessWindow t)).metric t

theorem selectedWindowMetric_eq (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) {t : ℝ}
    (ht : t ∈ shiftedCompactnessWindow j) :
    S.selectedWindowMetric P t = (S.identifiedWindowFlow P j).metric t :=
  S.identifiedWindowFlow_metric_compatible P _ j
    (selectedCompactnessWindow_mem (shiftedCompactnessWindow_subset j ht)) ht

theorem selectedWindowMetric_smooth (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    RiemannianMetric.IsSmoothFamilyOn (S.selectedWindowMetric P) (Iio 1) := by
  intro p hp
  let j := selectedCompactnessWindow p.1
  have hj : p.1 ∈ shiftedCompactnessWindow j := selectedCompactnessWindow_mem hp.1
  have hn : shiftedCompactnessWindow j ×ˢ
      (univ : Set (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier) ∈ 𝓝 p :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hj, mem_univ _⟩
  apply ContMDiffAt.contMDiffWithinAt
  apply ((S.identifiedWindowFlow P j).smooth.contMDiffAt hn).congr_of_eventuallyEq
  filter_upwards [hn] with q hq
  simp only [S.selectedWindowMetric_eq P j hq.1]

noncomputable def gluedShiftedAncientFlow (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    RicciFlow n (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier (Iio 1) where
  metric := S.selectedWindowMetric P
  connection t := (S.identifiedWindowFlow P (selectedCompactnessWindow t)).connection t
  interval := ordConnected_Iio
  nontrivial := ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  smooth := S.selectedWindowMetric_smooth P
  equation := by
    intro t ht x v w
    let j := selectedCompactnessWindow t
    have hj : t ∈ shiftedCompactnessWindow j := selectedCompactnessWindow_mem ht
    have hd := ((S.identifiedWindowFlow P j).equation t hj x v w).hasDerivAt
      (isOpen_Ioo.mem_nhds hj)
    apply HasDerivAt.hasDerivWithinAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hj] with s hs
    rw [S.selectedWindowMetric_eq P j hs]

theorem gluedShiftedAncientFlow_metric_eq (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) {t : ℝ}
    (ht : t ∈ shiftedCompactnessWindow j) :
    (S.gluedShiftedAncientFlow P).metric t = (S.identifiedWindowFlow P j).metric t := by
  change S.selectedWindowMetric P t = _
  exact S.selectedWindowMetric_eq P j ht

theorem gluedShiftedAncientFlow_complete (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {t : ℝ} (ht : t < 1) :
    MetricComplete ((S.gluedShiftedAncientFlow P).metric t) := by
  change MetricComplete ((S.identifiedWindowFlow P (selectedCompactnessWindow t)).metric t)
  exact S.identifiedWindowFlow_complete P _ (selectedCompactnessWindow_mem ht)

noncomputable def ancientWindowLimitFlow (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    RicciFlow n (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier (Iio 0) :=
  (S.gluedShiftedAncientFlow P).translate 1
    (by rintro t ⟨s, hs, rfl⟩; change s + 1 < 1; change s < 0 at hs; linarith)
    ordConnected_Iio ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩

theorem ancientWindowLimitFlow_metric_eq (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (compactnessLower j) (compactnessUpper j)) :
    (S.ancientWindowLimitFlow P).metric t = (S.identifiedWindowFlow P j).metric (t + 1) := by
  change (S.gluedShiftedAncientFlow P).metric (t + 1) = _
  exact S.gluedShiftedAncientFlow_metric_eq P j ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem ancientWindowLimitFlow_complete (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {t : ℝ} (ht : t < 0) :
    MetricComplete ((S.ancientWindowLimitFlow P).metric t) := by
  simpa only [ancientWindowLimitFlow, RicciFlow.translate] using
    S.gluedShiftedAncientFlow_complete P (t := t + 1) (by linarith)

end PoincareConjecture.AncientRescalingSequence
