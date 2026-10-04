import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Regular.TerminalRegularStageFamily

/-!
# The actual physical terminal projection of each regular chart

The whole dependent history map and the actual source inclusion identify
the same physical point. The zero clock is simplified only after that
identity, preserving the original chart and both source carriers.
MT Proposition 14.12; terminal-regular-finite-germs.md, I1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {S : RepairedControlledSchedulesData.{u}}
  {B : M47ComponentAnalyticBounds.{u} S.setup.C} {p : SurgeryParameterPrefix S.constants}
  {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {W : M33RegularHistoryWindow F}
  {H : M33RegularHistoryData W} {base Q r A tau0 tau K L a R rho : ℝ} {N : ℕ}
  {center : (F.slice base).carrier}
  (data : TerminalRegularStageData S B p O H base Q r A tau0 tau K L a R rho N center)
  (h0 : (0 : ℝ) ∈ Icc (-tau) 0)

/-- The actual chart projection and source history map are the same
dependent physical spacetime point before simplifying the zero clock. -/
theorem terminalSource_regular_terminal_sigma (i : Fin (N + 1))
    (x : terminalSourceCountableDomain rho) :
    (⟨base, (data.maps i x).val⟩ : (t : ℝ) × (F.slice t).carrier) =
      ⟨base + 0 / Q, H.history.forward (base + 0 / Q) (data.time 0 h0)
        (data.cylinder.forward 0 h0 ((data.cover.chart i).chart x.val).val)⟩ := by
  let U := terminalRegularStageSource F base Q A center
  let z : U := (data.cover.chart i).chart x.val
  let j := terminalSourceNormal_terminalMap U data.point
    (terminalSourceNormal_historyCylinder H U data.time data.cylinder) h0
  have hmap := terminalSourceNormal_history_terminal_map H U data.time data.cylinder
    data.point h0
  have hpoint := congrArg
    (fun q : (t : ℝ) × (U → (F.slice t).carrier) =>
      (⟨q.1, q.2 z⟩ : (t : ℝ) × (F.slice t).carrier)) hmap
  have hj : j z = (data.maps i x).val :=
    ((data.terminal h0).2.2 z).trans (data.projection i x).symm
  change (⟨base, j z⟩ : (t : ℝ) × (F.slice t).carrier) = _ at hpoint
  rw [hj] at hpoint
  exact hpoint

/-- The literal zero-time physical projection required by the original
finite-germ consumer follows from the retained actual history identity. -/
theorem terminalSource_regular_terminal_projection :
    let physical : Poincare.connectedComponentOpens E center →
        (F.slice (base + 0 / Q)).carrier := fun z => by
      simpa only [zero_div, add_zero] using z.val
    ∀ (i : Fin (N + 1)) (x : terminalSourceCountableDomain rho),
      physical (data.maps i x) = H.history.forward (base + 0 / Q) (data.time 0 h0)
        (data.cylinder.forward 0 h0 ((data.cover.chart i).chart x.val).val) := by
  let physical : Poincare.connectedComponentOpens E center →
      (F.slice (base + 0 / Q)).carrier := fun z => by
    simpa only [zero_div, add_zero] using z.val
  dsimp only
  intro i x
  have hcast : (⟨base + 0 / Q, physical (data.maps i x)⟩ : (t : ℝ) × (F.slice t).carrier) =
      ⟨base, (data.maps i x).val⟩ := by
    apply Sigma.ext
    · simp only [zero_div, add_zero]
    · dsimp only [physical]
      exact cast_heq _ _
  have hs := hcast.trans (terminalSource_regular_terminal_sigma data h0 i x)
  exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2

end PoincareMT.M47
