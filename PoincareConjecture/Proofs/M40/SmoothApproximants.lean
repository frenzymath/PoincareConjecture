import PoincareConjecture.Proofs.M40.GlobalSmoothing
import PoincareConjecture.Proofs.M40.Mathlib.PointCorrectionManifold
import PoincareConjecture.Statements.M40ComparisonHomotopy











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M40

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  {I : RepairedComparisonHomotopyInput D T hT}





theorem comparison_smooth_approximants
    (Q : RepairedComparisonMapConclusion I.toRepairedComparisonMapInput) :
    ∀ eta : ℝ, 0 < eta → ∃ d : ℝ, 0 < d ∧
      ∀ t : ℝ, T - d < t → t < T →
        ∃ f : C(I.parent.carrier.carrier, I.child.carrier.carrier),
          ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧
          f I.parent.basepoint = Q.target_basepoint ∧
          ContinuousMap.Homotopic f Q.map ∧
          ∀ x y, I.child_metric.edist (f x) (f y) ≤
            ENNReal.ofReal (1 + eta) * (I.parent_metric t).edist x y := by
  let : CompactSpace I.parent.carrier.carrier := isCompact_univ_iff.mp I.parent.compact
  let : CompactSpace I.child.carrier.carrier := isCompact_univ_iff.mp I.child.compact
  let : SimplyConnectedSpace I.parent.carrier.carrier := I.parent_simply_connected
  let : SimplyConnectedSpace I.child.carrier.carrier := I.child_simply_connected
  intro eta heta
  let theta : ℝ := min 1 (eta / 8)
  have htheta : 0 < theta := lt_min zero_lt_one (by positivity)
  have htheta1 : theta ≤ 1 := min_le_left _ _
  have hthetaeta : theta ≤ eta / 8 := min_le_right _ _
  have hbudget : (1 + theta) * (1 + theta + theta) ≤ 1 + eta := by
    nlinarith [mul_le_of_le_one_right htheta.le htheta1]
  obtain ⟨d, hd, _, hlate⟩ := Q.late_lipschitz theta htheta
  refine ⟨d, hd, fun t ht htT => ?_⟩
  obtain ⟨r, hr, hcorrect⟩ := exists_smooth_pointCorrected_map
    (I.parent_metric t) I.child_metric Q.target_basepoint htheta
  obtain ⟨f, hf, hhom, hclose, hbound⟩ := exists_smooth_approximation
    (I.parent_metric t) I.child_metric Q.map (L := 1 + theta)
    (epsilon := r) (sigma := theta) (by linarith) hr htheta (hlate t ht htT)
  have hbaseclose : I.child_metric.edist (f I.parent.basepoint) Q.target_basepoint <
      ENNReal.ofReal r := by
    rw [← Q.based]
    exact hclose I.parent.basepoint
  obtain ⟨f', hf', hbase, hhom', hbound'⟩ :=
    hcorrect f hf I.parent.basepoint hbaseclose (1 + theta + theta) hbound
  refine ⟨f', hf', hbase, hhom'.trans hhom, fun x y => (hbound' x y).trans ?_⟩
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl

end PoincareConjecture.M40
