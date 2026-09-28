import PoincareConjecture.Definitions.M39ComparisonMap








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedComparisonHomotopyInput
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (T : ℝ) (hT : T ∈ D.flow.surgery_times)
    [Nonempty (D.flow.slice T).carrier]
    extends RepairedComparisonMapInput D T hT where
  parent_simply_connected : SimplyConnectedSpace parent.carrier.carrier
  child_simply_connected : SimplyConnectedSpace child.carrier.carrier
  parent_orientation :
    surgeryThirdHomology parent.carrier.carrier ≃ₗ[ℤ] ULift.{u} ℤ

structure RepairedComparisonHomotopyConclusion
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {T : ℝ} {hT : T ∈ D.flow.surgery_times}
    [Nonempty (D.flow.slice T).carrier]
    (I : RepairedComparisonHomotopyInput D T hT) where
  comparison : RepairedComparisonMapConclusion I.toRepairedComparisonMapInput
  child_orientation :
    surgeryThirdHomology I.child.carrier.carrier ≃ₗ[ℤ] ULift.{u} ℤ
  degree_one : ∀ z : surgeryThirdHomology I.parent.carrier.carrier,
    child_orientation (surgeryThirdHomologyMap comparison.map z) =
      I.parent_orientation z
  homotopy_equivalence : ∃ e : ContinuousMap.HomotopyEquiv
    I.parent.carrier.carrier I.child.carrier.carrier,
    e.toFun = comparison.map
  pi_three_bijective : Function.Bijective
    (surgeryHomotopyMap (n := 3) comparison.map comparison.based)
  smooth_approximants : ∀ eta : ℝ, 0 < eta → ∃ d : ℝ, 0 < d ∧
    ∀ t : ℝ, T - d < t → t < T →
      ∃ f : ContinuousMap I.parent.carrier.carrier I.child.carrier.carrier,
        ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧
        (∃ hbase : f I.parent.basepoint = comparison.target_basepoint,
          ∀ alpha, surgeryHomotopyMap (n := 3) f hbase alpha =
            surgeryHomotopyMap comparison.map comparison.based alpha) ∧
        ContinuousMap.Homotopic f comparison.map ∧
        (∀ x y, I.child_metric.edist (f x) (f y) ≤
          ENNReal.ofReal (1 + eta) * (I.parent_metric t).edist x y) ∧
        (∀ z : surgeryThirdHomology I.parent.carrier.carrier,
          child_orientation (surgeryThirdHomologyMap f z) =
            I.parent_orientation z)

structure RepairedComparisonHomotopyData
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (K : RepairedComparisonMapData D) where
  transport : ∀ (T : ℝ) (hT : T ∈ D.flow.surgery_times)
      [Nonempty (D.flow.slice T).carrier],
      ∀ I : RepairedComparisonHomotopyInput D T hT,
        ∀ hdelta : D.flow.parameters.delta T < repairedComparisonDeltaBound
          D.flow.local_constants,
          ∀ hh : D.flow.parameters.h T < repairedComparisonHeightBound
            D.flow.local_constants,
          Nonempty {O : RepairedComparisonHomotopyConclusion I //
            O.comparison = Classical.choice
              (K.comparison T hT I.toRepairedComparisonMapInput hdelta hh)}

end PoincareConjecture
