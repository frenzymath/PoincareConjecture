import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Positive.PositiveHistory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.PositiveComponents.PositiveCylinderLines

/-!
# Nonpositive ancestors of an actual cap-contact birth

Positivity along an actual retained cylinder line would reach the literal
pre-event endpoint. Its retained child meets an inserted cap, contradicting
whole positive-component retention. Source: Morgan--Tian, pp. 393-394.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M47Positive

/-- Every earlier reached point of an actual cylinder ending at a retained
preimage of a cap-contact child is nonpositive. The endpoint equality,
retained membership and cap contact are literal physical data; MT pp. 393-394. -/
theorem ancestor_nonpositive_of_retained_child_meets_cap
    (hC : RicciFlowCurvatureTheory.{u}) (F : SurgeryFlowData.{u})
    {J : Set ℝ} (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T : ℝ} (hTJ : T ∈ J) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U) {x : C.carrier} (hx : x ∈ U)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b)
    (hv : origin + b / scale ∈ Ico (F.event T hT).tMinus T)
    (q : (F.slice (F.event T hT).tMinus).carrier)
    (hendpoint : e.forward b hb x =
      (F.event T hT).pre_identify ⟨origin + b / scale, hv⟩ q)
    (hretained : q ∈ (F.event T hT).retained_pre)
    {i : Fin (F.event T hT).cap_count}
    (hcontact : (connectedComponent ((F.event T hT).retention.map q) ∩
      ((F.event T hT).caps i).carrier).Nonempty) :
    ¬ SurgeryPositiveComponentAt F (origin + a / scale) (e.forward a ha x) := by
  intro hpos
  have hterminal := Proofs.M46.positive_component_cylinder_line e hx ha hb hab hpos
  rw [hendpoint] at hterminal
  exact pre_component_nonpositive_of_retained_child_meets_cap hC F hpolicy hTJ hT
    ⟨origin + b / scale, hv⟩ q hretained hcontact hterminal

end PoincareMT.M47Positive
