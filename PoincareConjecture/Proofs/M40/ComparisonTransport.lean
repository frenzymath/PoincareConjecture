import PoincareConjecture.Proofs.M40.HomotopyEquivalence
import PoincareConjecture.Proofs.M40.PiThree










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M40

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  {I : RepairedComparisonHomotopyInput D T hT}




noncomputable def comparisonHomotopyConclusion
    (P : RepairedClosedTopologyProvider.{u})
    (Q : RepairedComparisonMapConclusion I.toRepairedComparisonMapInput)
    (hsmooth : ∀ eta : ℝ, 0 < eta → ∃ d : ℝ, 0 < d ∧
      ∀ t : ℝ, T - d < t → t < T →
        ∃ f : C(I.parent.carrier.carrier, I.child.carrier.carrier),
          ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧
          f I.parent.basepoint = Q.target_basepoint ∧
          ContinuousMap.Homotopic f Q.map ∧
          ∀ x y, I.child_metric.edist (f x) (f y) ≤
            ENNReal.ofReal (1 + eta) * (I.parent_metric t).edist x y) :
    RepairedComparisonHomotopyConclusion I where
  comparison := Q
  child_orientation := comparisonChildOrientation Q
  degree_one := comparison_degree_one Q
  homotopy_equivalence := comparison_homotopy_equivalence Q P
  pi_three_bijective := by
    let : SimplyConnectedSpace I.parent.carrier.carrier := I.parent_simply_connected
    let : SimplyConnectedSpace I.child.carrier.carrier := I.child_simply_connected
    exact Proofs.M40.surgeryPiThree_bijective_of_homotopyEquiv Q.map Q.based
      (comparison_homotopy_equivalence Q P)
  smooth_approximants := by
    let : SimplyConnectedSpace I.child.carrier.carrier := I.child_simply_connected
    intro eta heta
    obtain ⟨d, hd, happ⟩ := hsmooth eta heta
    refine ⟨d, hd, ?_⟩
    intro t ht htT
    obtain ⟨f, hf, hbase, hhom, hbound⟩ := happ t ht htT
    exact ⟨f, hf,
      ⟨hbase, Proofs.M40.surgeryHomotopyMap_eq_of_homotopic f Q.map hbase Q.based hhom⟩,
      hhom, hbound, comparison_degree_one_of_homotopic Q hhom⟩

end PoincareConjecture.M40
