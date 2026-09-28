import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCylinderJoin
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialTop










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem exists_source_initial_closed_cylinder
    {F : SurgeryFlowData.{u}} {T left : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    (old : SurgeryTerminalStrongNeck F T hT i)
    {U V : Set (F.event T hT).terminal.carrier}
    (D : SurgeryFlowCylinder F (F.event T hT).terminal T
      (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) (Icc left (-1 / 2)) U)
    (hleft : left ≤ -1 / 2) (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U)
    (hnegative : V ⊆ ((F.event T hT).necks i).neck.region
      (-((F.event T hT).necks i).neck.epsilon⁻¹) 0)
    (hagree : ∀ s (hs : s ∈ Icc left (-1 / 2)) (hs' : s ∈ Ioo (-1 : ℝ) 0),
      ∀ x ∈ U, D.forward s hs x = old.cylinder.forward s hs' x) :
    ∃ E : SurgeryFlowCylinder F (F.event T hT).terminal T
        (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) (Icc left 0) V,
      (∀ s (hs : s ∈ Icc left (-1 / 2)) (hs' : s ∈ Icc left 0),
        ∀ x ∈ V, E.forward s hs' x = D.forward s hs x) ∧
      (∀ s (hs : s ∈ Ioo (-1 : ℝ) 0) (hs' : s ∈ Icc left 0),
        ∀ x ∈ V, E.forward s hs' x = old.cylinder.forward s hs x) ∧
      ∀ hs x, HEq (E.forward 0 hs x)
        ((F.event T hT).retention.map ((F.event T hT).limit_identify.inverse x)) := by
  obtain ⟨top, htopOld, htopZero⟩ :=
    exists_source_initial_retained_top hT i old V hV hnegative
  have htopInterval : Icc (-1 / 2 : ℝ) 0 ⊆ Ioc (-1 : ℝ) 0 := by
    intro s hs
    exact ⟨lt_of_lt_of_le (by norm_num) hs.1, hs.2⟩
  let past := D.restrict Subset.rfl ordConnected_Icc hVU
  let future := top.restrict htopInterval ordConnected_Icc (Subset.refl V)
  have hjoin : ∀ x ∈ V, past.forward (-1 / 2) ⟨hleft, le_rfl⟩ x =
      future.forward (-1 / 2) (by norm_num) x := by
    intro x hx
    change D.forward (-1 / 2) _ x = top.forward (-1 / 2) _ x
    rw [hagree (-1 / 2) _ (by norm_num) x (hVU hx)]
    exact (htopOld (-1 / 2) (by norm_num) _ x).symm
  obtain ⟨E, hfuture, hpast⟩ := exists_source_initial_joined_cylinder
    past future hleft (by norm_num) hV hne hjoin
  refine ⟨E, ?_, ?_, ?_⟩
  · intro s hs hs' x hx
    exact hpast s hs hs' x hx
  · intro s hs hs' x hx
    by_cases hhalf : s ≤ -1 / 2
    · exact (hpast s ⟨hs'.1, hhalf⟩ hs' x hx).trans
        (hagree s ⟨hs'.1, hhalf⟩ hs x (hVU hx))
    · have ht : s ∈ Icc (-1 / 2 : ℝ) 0 := ⟨(lt_of_not_ge hhalf).le, hs.2.le⟩
      exact (hfuture s ht hs' x).trans (htopOld s hs _ x)
  · intro hs x
    exact (heq_of_eq (hfuture 0 (by norm_num) hs x)).trans (htopZero _ x)

end PoincareConjecture.M47
