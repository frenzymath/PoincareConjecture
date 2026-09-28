import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_InitialCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_MaximalCylinderStopping










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44





theorem exists_stopped_based_cylinder
    (P : M44CapPersistencePredecessors.{u}) (F : SurgeryFlowData.{u})
    (hpinch : SurgeryFlowPinched F) {origin scale B : ℝ}
    (hscale : 0 < scale) (hB : 0 < B)
    (htime : ∀ s ∈ Ico 0 B, origin + s / scale ∈ F.time_domain)
    (U : Set (F.slice origin).carrier) (hU : IsOpen U) :
    ∃ c : ℝ, 0 < c ∧ c ≤ B ∧
      ∃ e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U,
        (∀ h x, x ∈ U → HEq (e.forward 0 h x) x) ∧
        (c = B ∨ ∃ hT : origin + c / scale ∈ F.surgery_times,
          IsEmpty (F.slice (origin + c / scale)).carrier ∨
          ∃ _hn : Nonempty (F.slice (origin + c / scale)).carrier,
            ∃ x ∈ U, ∀ s (hs : s ∈ Ico 0 c),
              ∀ ht : origin + s / scale ∈
                Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale),
                ((F.event (origin + c / scale) hT).pre_identify
                  ⟨origin + s / scale, ht⟩).symm (e.forward s hs x) ∉
                    interior (F.event (origin + c / scale) hT).retained_pre) := by
  classical
  obtain ⟨b0, hb0, hb0B, e0, hinit0⟩ :=
    exists_initial_based_cylinder F hscale hB htime U
  obtain ⟨c, hc, hcB, e, hinitial, _, hstop⟩ :=
    exists_maximal_based_cylinder e0 hb0 hb0B.le hinit0
  refine ⟨c, hc, hcB, e, hinitial, ?_⟩
  by_cases hceq : c = B
  · exact Or.inl hceq
  · have hclt : c < B := lt_of_le_of_ne hcB hceq
    have hT := maximal_cylinder_endpoint_is_surgery e hU hc hclt htime hinitial hstop
    refine Or.inr ⟨hT, ?_⟩
    by_cases hn : Nonempty (F.slice (origin + c / scale)).carrier
    · exact Or.inr ⟨hn, maximal_cylinder_has_fixed_lost_line P hpinch e hU hc hclt
        htime hinitial hstop hT⟩
    · exact Or.inl ⟨fun x => hn ⟨x⟩⟩

end PoincareConjecture.M44
