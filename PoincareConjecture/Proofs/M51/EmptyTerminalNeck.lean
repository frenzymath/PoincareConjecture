import PoincareConjecture.Proofs.M51.EmptyExtension
import PoincareConjecture.Proofs.M48.ExtensionCylinderMetric
import PoincareConjecture.Proofs.M48.RoundCylinderCongruence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier] (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] [Nonempty ((flow F ha).slice T).carrier]

noncomputable def terminalStrongNeck (i : Fin (F.event T hT).cap_count)
    (N : SurgeryTerminalStrongNeck F T hT i) :
    SurgeryTerminalStrongNeck (flow F ha) T hT i := by
  let E := F.event T hT
  let d := (extension F ha).pushCylinder N.cylinder
  refine ⟨d, ?_, ?_⟩
  · intro s hs ht x hx
    change T + s / (E.necks i).neck.scale⁻¹ ^ 2 ∈ Ico E.tMinus T at ht
    change identify F ha (T + s / (E.necks i).neck.scale⁻¹ ^ 2)
      (N.cylinder.time_subset ⟨s, hs, rfl⟩)
      (N.cylinder.forward s hs x) =
      (E.reindexPast (fun t => min t a) (event_clock F ha T hT)).pre_identify
        ⟨T + s / (E.necks i).neck.scale⁻¹ ^ 2, ht⟩ ((E.reindexPast (fun t => min t a)
          (event_clock F ha T hT)).limit_identify.inverse x)
    rw [N.reference_compatibility s hs ht x hx,
      identify_of_le F ha _ _ (ht.2.le.trans (F.surgeryTime_le_empty ha hT)),
      E.reindexPast_limit_identify_inverse]
    exact (E.reindexPast_pre_identify_apply (fun t => min t a)
      (event_clock F ha T hT) ⟨_, ht⟩ (E.limit_identify.inverse x)).symm
  · apply RoundCylinderFamilyClose.congr (B' := fun s => if s = 0 then
        fun z v w => (E.necks i).neck.scale⁻¹ ^ 2 *
          roundCylinderPullback E.limit_metric (E.necks i).neck.coordinate_map z v w
        else surgeryCylinderPullback N.cylinder (E.necks i).neck.coordinate_map s)
      ?_ N.comparison
    intro s hs z hz v w
    by_cases hs0 : s = 0
    · simp only [hs0]
      rfl
    · have hs' : s ∈ Ioo (-1 : ℝ) 0 := ⟨hs.1, lt_of_le_of_ne hs.2 hs0⟩
      have hz' : z.2 ∈ Ioo (-(E.necks i).neck.epsilon⁻¹)
          (E.necks i).neck.epsilon⁻¹ := by
        simpa only [E.neck_delta] using hz
      have hcoord : (E.necks i).neck.coordinate_map z ∈ (E.necks i).neck.carrier := by
        have h := (E.necks i).neck.coordinate_map_eq (z.1, ⟨z.2, hz'⟩)
        exact h ▸ ((E.necks i).neck.coordinate (z.1, ⟨z.2, hz'⟩)).property
      simp only [if_neg hs0, surgeryCylinderPullback, dif_pos hs']
      exact (extension F ha).pushCylinder_pullbackInner N.cylinder
        (E.necks i).neck.carrier_open s hs' _ hcoord _ _

end PoincareConjecture.M51Empty
