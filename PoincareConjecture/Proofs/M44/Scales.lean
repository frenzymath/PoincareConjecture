import PoincareConjecture.Definitions.Ch16.NoncollapseInduction








set_option autoImplicit false

universe u

namespace PoincareConjecture




theorem SurgeryPrefixControls.capPersistenceScales
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {rNext deltaUpper : ℝ}
    (old : SurgeryPrefixControls p F O)
    (horizon : O.H ≤ surgeryEpochStart (p.i + 1))
    (hr : rNext ≤ p.r (Fin.last p.i))
    (next : SurgeryPostPrefixScales p F O rNext deltaUpper)
    (overlap : ∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
      F.parameters.delta t ≤ deltaUpper) :
    SurgeryFixedScalesOn p.setup F O
      (surgeryEpochStart (p.i - 1)) rNext deltaUpper := by
  have before : ∀ t ∈ surgeryObservationInterval O ∩
      Set.Ici (surgeryEpochStart (p.i - 1)),
      t < surgeryEpochStart p.i →
        t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry p.i := by
    intro t ht htEnd
    refine ⟨ht.1, ?_⟩
    simpa only [surgeryEpochEntry, Nat.ne_of_gt p.i_pos, if_false, Set.mem_Ico,
      Set.mem_Ici]
      using And.intro ht.2 htEnd
  refine {
    standard_initial_eq := old.standard_initial_eq
    local_constants_eq := old.local_constants_eq
    epsilon_eq := old.epsilon_eq
    C_eq := old.C_eq
    r_lower := ?_
    delta_le := ?_
    h_eq := ?_
  }
  · intro t ht
    by_cases htEnd : t < surgeryEpochStart p.i
    · rw [old.r_schedule (Fin.last p.i) (by simp) t (before t ht htEnd)]
      exact hr
    · rw [next.r_eq t ⟨ht.1, le_of_not_gt htEnd⟩]
  · intro t ht
    exact overlap t ⟨ht.1, ht.2, ht.1.2.trans_le horizon⟩
  · intro t ht
    by_cases htEnd : t < surgeryEpochStart p.i
    · exact old.h_schedule (Fin.last p.i) (by simp) t (before t ht htEnd)
    · exact next.h_eq t ⟨ht.1, le_of_not_gt htEnd⟩

end PoincareConjecture
