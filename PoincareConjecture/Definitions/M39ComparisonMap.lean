import PoincareConjecture.Definitions.Ch15.SurgeryComparison
import PoincareConjecture.Definitions.M38LocalTopology

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedComparisonMapInput
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (T : ℝ) (hT : T ∈ D.flow.surgery_times)
    [Nonempty (D.flow.slice T).carrier] where
  topology : RepairedNonemptyTopologyWitness D T hT
  parent : SurgerySelectedComponent (D.flow.slice (D.flow.event T hT).tMinus)
  child : SurgerySelectedComponent (D.flow.slice T)
  topology_child : ∃ i : Fin topology.conclusion.piece_count,
    topology.conclusion.kind i = .survivor ∧
      topology.conclusion.survivor_region i = Set.range child.inclusion
  admissible : SurgeryFlowAdmissible D.flow
  parent_metric : ℝ → RiemannianMetric 3 parent.carrier.carrier
  child_metric : RiemannianMetric 3 child.carrier.carrier
  parent_pullback : ∀ t : Set.Ico (D.flow.event T hT).tMinus T,
    ∀ x v w, ((D.flow.event T hT).pre_flow.metric t.1).inner (parent.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) parent.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) parent.inclusion x w) =
        (parent_metric t.1).inner x v w
  child_pullback : ∀ x v w, (D.flow.metric T).inner (child.inclusion x)
    (mfderiv (𝓡 3) (𝓡 3) child.inclusion x v)
    (mfderiv (𝓡 3) (𝓡 3) child.inclusion x w) = child_metric.inner x v w
  separating : ∀ i : Fin (D.flow.event T hT).cap_count,
    (parent.inclusion ⁻¹' ((D.flow.event T hT).limit_identify.inverse ''
      ((D.flow.event T hT).necks i).neck.central_sphere)).Nonempty →
    SeparatingSphere
      (parent.inclusion ⁻¹' ((D.flow.event T hT).limit_identify.inverse ''
        ((D.flow.event T hT).necks i).neck.central_sphere))
  retained : Set parent.carrier.carrier

  retained_eq : retained =
    {x | parent.inclusion x ∈ interior (D.flow.event T hT).retained_pre ∧
      (D.flow.event T hT).retention.map (parent.inclusion x) ∈
        Set.range child.inclusion}
  retained_open : IsOpen retained
  retained_subset : ∀ x ∈ retained,
    parent.inclusion x ∈ interior (D.flow.event T hT).retained_pre
  retained_to_child : ∀ x ∈ retained,
      (D.flow.event T hT).retention.map (parent.inclusion x) ∈ Set.range child.inclusion
  inherited : retained.Nonempty

structure RepairedComparisonMapConclusion
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {T : ℝ} {hT : T ∈ D.flow.surgery_times}
    [Nonempty (D.flow.slice T).carrier]
    (I : RepairedComparisonMapInput D T hT) where
  map : ContinuousMap I.parent.carrier.carrier I.child.carrier.carrier
  target_basepoint : I.child.carrier.carrier
  based : map I.parent.basepoint = target_basepoint
  retained_agreement : ∀ x ∈ I.retained,
    I.child.inclusion (map x) = (D.flow.event T hT).retention.map
      (I.parent.inclusion x)
  retained_open : IsOpen I.retained
  retained_target_open : IsOpen (I.child.inclusion '' map '' I.retained)
  retained_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map I.retained
  retained_metric : ∀ x ∈ I.retained, ∀ v w : TangentSpace (𝓡 3) x,
    I.child_metric.inner (map x)
      (mfderiv (𝓡 3) (𝓡 3) map x v)
      (mfderiv (𝓡 3) (𝓡 3) map x w) =
      (D.flow.event T hT).limit_metric.inner
        ((D.flow.event T hT).limit_identify.map (I.parent.inclusion x))
        (mfderiv (𝓡 3) (𝓡 3) (D.flow.event T hT).limit_identify.map
          (I.parent.inclusion x) (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x v))
        (mfderiv (𝓡 3) (𝓡 3) (D.flow.event T hT).limit_identify.map
          (I.parent.inclusion x) (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x w))
  distance_window : ℝ
  distance_window_pos : 0 < distance_window
  distance_window_le : distance_window ≤ T - (D.flow.event T hT).tMinus
  outside_image_in_caps : ∀ x ∉ I.retained,
    ∃ i : Fin (D.flow.event T hT).cap_count,
      I.child.inclusion (map x) ∈ ((D.flow.event T hT).caps i).carrier
  late_lipschitz : ∀ eta : ℝ, 0 < eta →
    ∃ d : ℝ, 0 < d ∧ d ≤ distance_window ∧
      ∀ t : ℝ, T - d < t → t < T →
        ∀ x y,
          I.child_metric.edist (map x) (map y) ≤
            ENNReal.ofReal (1 + eta) * (I.parent_metric t).edist x y

noncomputable def repairedComparisonDeltaBound
    (K : MetricSurgeryConstants) : ℝ := K.delta₀

noncomputable def repairedComparisonHeightBound
    (K : MetricSurgeryConstants) : ℝ := K.R₀ ^ (-1 / 2 : ℝ)

structure RepairedComparisonMapData
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀) where
  comparison : ∀ (T : ℝ) (hT : T ∈ D.flow.surgery_times)
      [Nonempty (D.flow.slice T).carrier],
      ∀ I : RepairedComparisonMapInput D T hT,
        D.flow.parameters.delta T < repairedComparisonDeltaBound
          D.flow.local_constants →
        D.flow.parameters.h T < repairedComparisonHeightBound
          D.flow.local_constants →
        Nonempty (RepairedComparisonMapConclusion I)

end PoincareConjecture
