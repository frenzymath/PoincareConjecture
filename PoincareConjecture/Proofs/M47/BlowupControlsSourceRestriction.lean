import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Definitions.Ch16.CapPersistence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem restrict_cap_family_comparison
    {F : SurgeryFlowData.{u}} {S : MaximalStandardCapFlow F.standard_initial}
    {t eta A a : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (ha : 0 < a) (haa : a ≤ A) :
    ∃ small : SurgeryCapInitialComparison F t hT i a,
      ∃ esmall : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
          J (initial.chart '' F.standard_initial.metric.ball 0 a),
        SurgeryCapFamilyComparison F S a eta esmall small.chart ∧
          small.chart = initial.chart ∧ small.inverse = initial.inverse := by
  have hA : 0 < A := initial.A_pos
  have hball : F.standard_initial.metric.ball 0 a ⊆
      F.standard_initial.metric.ball 0 A := by
    intro x hx
    change F.standard_initial.metric.edist 0 x < ENNReal.ofReal A
    have hx' : F.standard_initial.metric.edist 0 x < ENNReal.ofReal a := hx
    exact hx'.trans_le (ENNReal.ofReal_le_ofReal haa)
  have himage : initial.chart '' F.standard_initial.metric.ball 0 a ⊆ U := by
    rw [← (comparison.choose_spec.2.2.2.1 :
      initial.chart '' F.standard_initial.metric.ball 0 A = U)]
    exact image_mono hball
  let small : SurgeryCapInitialComparison F t hT i a := {
    A_pos := ha
    chart := initial.chart
    inverse := initial.inverse
    chart_smooth := initial.chart_smooth.mono hball
    inverse_smooth := initial.inverse_smooth
    left_inverse := by
      intro x hx
      exact initial.left_inverse (hball hx)
    right_inverse := by
      intro y hy
      exact initial.right_inverse hy
    tip_eq := initial.tip_eq
    local_metric_link := by
      obtain ⟨kappa, hkappa, Q, hdelta, hcontain, hmap⟩ :=
        initial.local_metric_link
      refine ⟨kappa, hkappa, Q, hdelta, ?_, ?_⟩
      · exact hball.trans hcontain
      · intro x hx
        exact hmap x (hball hx)
  }
  let esmall := e.restrict Subset.rfl e.interval_connected himage
  have hsmall_chart : small.chart = initial.chart := rfl
  have hsmall_inverse : small.inverse = initial.inverse := rfl
  obtain ⟨bound, hbound, hlifetime, hinterval, _himage, hjet⟩ := comparison
  refine ⟨small, esmall, ?_, hsmall_chart, hsmall_inverse⟩
  refine ⟨bound, hbound, hlifetime, hinterval, rfl, ?_⟩
  intro s hs x hx
  exact hjet s hs x (hball hx)

end PoincareConjecture.M47
