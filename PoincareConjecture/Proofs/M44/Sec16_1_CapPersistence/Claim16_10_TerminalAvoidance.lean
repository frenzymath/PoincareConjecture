import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_PreterminalStopping










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c : ℝ} {U : Set C.carrier}




theorem preterminal_neck_avoidance_of_terminal
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale))
    (havoid : ∀ i, Disjoint (cylinderTerminalChart e hU hT r hr hr' '' U)
      ((F.event (origin + c / scale) hT).necks i).neck.central_sphere)
    (s : ℝ) (hs : s ∈ Ico 0 c)
    (hs' : origin + s / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale)) (i : Fin (F.event (origin + c / scale) hT).cap_count) :
    Disjoint ((fun x => ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + s / scale, hs'⟩).symm (e.forward s hs x)) '' U)
      ((F.event (origin + c / scale) hT).limit_identify.inverse ''
        ((F.event (origin + c / scale) hT).necks i).neck.central_sphere) := by
  apply disjoint_left.mpr
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  change (F.event (origin + c / scale) hT).limit_identify.inverse y =
    ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + s / scale, hs'⟩).symm (e.forward s hs x) at heq
  have hfixed := cylinder_preterminal_coordinates_eq_of_pinched P hpinch e hT
    s hs r hr hs' hr' x hx
  have hterminal : cylinderTerminalChart e hU hT r hr hr' x = y := by
    change (F.event (origin + c / scale) hT).limit_identify.map
      (((F.event (origin + c / scale) hT).pre_identify
        ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)) = y
    rw [← hfixed, ← heq]
    exact (F.event (origin + c / scale) hT).limit_identify.right_inverse (mem_univ y)
  apply disjoint_left.mp (havoid i) (mem_image_of_mem _ hx)
  rwa [hterminal]




theorem disappears_of_terminal_neck_avoidance
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hconnected : IsPreconnected U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale))
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hlost : ∃ x ∈ U, ∀ s (hs : s ∈ Ico 0 c),
      ∀ ht : origin + s / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale),
        ((F.event (origin + c / scale) hT).pre_identify
          ⟨origin + s / scale, ht⟩).symm (e.forward s hs x) ∉
            interior (F.event (origin + c / scale) hT).retained_pre)
    (havoid : ∀ i, Disjoint (cylinderTerminalChart e hU hT r hr hr' '' U)
      ((F.event (origin + c / scale) hT).necks i).neck.central_sphere) :
    SurgeryBallDisappearsAt F e (origin + c / scale) :=
  disappears_of_fixed_lost_line e (hr.1.trans_lt hr.2) hconnected hT hinitial hlost
    (preterminal_neck_avoidance_of_terminal P hpinch e hU hT r hr hr' havoid)

end PoincareConjecture.M44
