import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.PositiveComponents.PositiveHistoryPaths

/-!
# The connected flow-box neighborhood of the actual path

The original atlas supplies the endpoint coordinate and an open
connected-component image. Source: MT p. 393;
derivations/seed-m15-ancestry.md, Stages I5-I6.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareMT.M47

open Proofs.M46

/-- The actual continuous path lies near an included point in the
connected spatial component of that point's original flow box. -/
theorem seedM15_path_component_box
    (G : GeneralizedRicciFlowData.{u}) {I : Set ℝ} {b : ℝ}
    (gamma : ℝ → G.point) (hcont : ContinuousOn gamma I) (hb : b ∈ I)
    (hclock : (gamma b).1 = b) :
    ∃ q : G.box_index, ∃ x : (G.box q).carrier.carrier,
      ∃ hbox : b ∈ (G.box q).interval,
        gamma b = (⟨b, (G.box q).forward b hbox x⟩ : G.point) ∧
        ∀ᶠ t in 𝓝[I] b, gamma t ∈ componentBoxImage G ⟨q, x⟩ := by
  obtain ⟨q, hbox0, x, hx⟩ := G.box_covers (gamma b).1 (gamma b).2
  have hbox : b ∈ (G.box q).interval := hclock ▸ hbox0
  have hpoint0 : (⟨(gamma b).1, (G.box q).forward (gamma b).1 hbox0 x⟩ : G.point) =
      gamma b := Sigma.ext rfl (heq_of_eq hx)
  have hcast := congrArg
    (fun t : (G.box q).interval => (⟨t.val, (G.box q).forward t.val t.property x⟩ : G.point))
    (show (⟨(gamma b).1, hbox0⟩ : (G.box q).interval) = ⟨b, hbox⟩ from
      Subtype.ext hclock)
  have hpoint : (⟨b, (G.box q).forward b hbox x⟩ : G.point) = gamma b :=
    hcast.symm.trans hpoint0
  have hmem : gamma b ∈ componentBoxImage G ⟨q, x⟩ :=
    ⟨(⟨b, hbox⟩, x), ⟨mem_univ _, mem_connectedComponent⟩, hpoint⟩
  refine ⟨q, x, hbox, hpoint.symm, ?_⟩
  exact (hcont b hb) ((componentBoxImage_isOpen G ⟨q, x⟩).mem_nhds hmem)

/-- Positivity at a point of a connected spatial box component gives
positivity on its fixed central line at the same actual time. -/
theorem seedM15_historyPositive_box_line
    {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
    (H : M33RegularHistoryRealization G F)
    (q : G.box_index) (x : (G.box q).carrier.carrier) {p : G.point}
    (hp : p ∈ componentBoxImage G ⟨q, x⟩) (hpos : HistoryPositive H p) :
    ∃ ht : p.1 ∈ (G.box q).interval,
      SurgeryPositiveComponentAt F p.1
        (H.forward p.1 (m33BoxIntervalSubset G q ht) ((G.box q).forward p.1 ht x)) := by
  obtain ⟨⟨t, y⟩, ⟨_, hy⟩, rfl⟩ := hp
  have hxy : x ∈ connectedComponent y := by
    rw [← connectedComponent_eq hy]
    exact mem_connectedComponent
  exact ⟨t.property, positive_component_history_box_connected H q hxy
    t.property t.property le_rfl (hpos (m33BoxIntervalSubset G q t.property))⟩

/-- The same box-line conclusion at the literal physical path time. -/
theorem seedM15_historyPositive_box_line_at
    {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
    (H : M33RegularHistoryRealization G F)
    (q : G.box_index) (x : (G.box q).carrier.carrier) {p : G.point} {t : ℝ}
    (hclock : p.1 = t) (hp : p ∈ componentBoxImage G ⟨q, x⟩)
    (hpos : HistoryPositive H p) :
    ∃ ht : t ∈ (G.box q).interval,
      SurgeryPositiveComponentAt F t
        (H.forward t (m33BoxIntervalSubset G q ht) ((G.box q).forward t ht x)) := by
  subst t
  exact seedM15_historyPositive_box_line H q x hp hpos

end PoincareMT.M47
