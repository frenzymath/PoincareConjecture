import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventTopology

/-!
The source M38 constructor accepts the doubled-epsilon bound. Apply it
under the workspace's reviewed terminal-accuracy bound without changing either
the constructor or the reviewed surgery-topology interface.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.SurgeryTopology

theorem exists_raw_topology_of_terminal_accuracy
    (N : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ N.epsilon₀ ∧
      ∀ F : SurgeryFlowData.{u}, SurgeryFlowAdmissible F →
        terminalAccuracyFactor * F.parameters.epsilon ≤ epsilon0 →
        Nonempty (RawLocalSurgeryTopologyData F) := by
  obtain ⟨epsilon0, hpos, hbound, hraw⟩ := M38.exists_raw_local_surgery_topology_data N
  refine ⟨epsilon0, hpos, hbound, ?_⟩
  intro F hF hepsilon
  apply hraw F hF
  exact (mul_le_mul_of_nonneg_right two_le_terminalAccuracyFactor
    F.parameters.epsilon_pos.le).trans hepsilon

end PoincareMT.SurgeryTopology

namespace PoincareMT.M38ReviewedAccuracy

scoped macro "M38.exists_raw_local_surgery_topology_data" : term =>
  `(PoincareMT.SurgeryTopology.exists_raw_topology_of_terminal_accuracy)

end PoincareMT.M38ReviewedAccuracy
