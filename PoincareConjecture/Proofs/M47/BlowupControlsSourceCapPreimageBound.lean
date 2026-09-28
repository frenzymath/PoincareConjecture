import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthCenter

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem source_cap_preimage_initial_radius
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {R A eta : ℝ}
    (hR : 0 < R) (hRA : R ≤ A) (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000)
    {J : Set ℝ}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
      ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J)
    (based : ∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip
      (A * F.parameters.h t), HEq (e.forward 0 hzero y) y)
    {z : StandardCapSpace} (hz : z ∈ F.standard_initial.metric.ball 0 A)
    (hcaptured : initial.chart z ∈ (F.metric t).ball ((F.event t hT).caps i).tip
      (R * F.parameters.h t)) :
    F.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * R) := by
  obtain ⟨z0, hz0, heq, hbound⟩ := exists_cap_birth_center_in_fixed_ball hR hRA
    heta hetaSmall e initial comparison hzero based hcaptured
  have hsame : z0 = z := by
    calc
      z0 = initial.inverse (initial.chart z0) := (initial.left_inverse hz0).symm
      _ = initial.inverse (initial.chart z) := congrArg initial.inverse heq
      _ = z := initial.left_inverse hz
  simpa only [hsame] using hbound

end PoincareConjecture.M47
