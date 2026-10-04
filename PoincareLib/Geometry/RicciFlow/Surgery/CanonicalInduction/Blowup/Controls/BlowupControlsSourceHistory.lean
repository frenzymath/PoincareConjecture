import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceSearch
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeCylinder
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Source.TerminalSourceNormalHistory

/-!
# The actual closed interior of the retained search

The larger constructed search gives an earlier parameter at every time
of the requested closed slab. M33 therefore lifts the complete slab to
the same selected history. Its literal terminal map is the inclusion
of the original physical source. Source: Morgan--Tian Proposition 14.12
and Claim 17.9, pp. 350 and 406; blowup-source-survival.md, Stage S2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

/-- The original earlier parameter supplies regularity at both included
endpoints; the actual lifted terminal map has exactly the original range. -/
theorem exists_regular_history_search_interior
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {base Q a tau : ℝ}
    (hbase : base ∈ H.generalized.interval) (htau : 0 < tau) (ha : a < -tau)
    (U : TopologicalSpace.Opens (F.slice base).carrier) (p0 : U)
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0) U)
    (hbased : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x) :
    ∃ htime : ∀ s ∈ Icc (-tau) 0, base + s / Q ∈ H.generalized.interval,
      ∃ d : GeneralizedFlowCylinder H.generalized (F.slice base) base Q
          (Icc (-tau) 0) U,
        (∀ s hs x, x ∈ U → H.history.forward (base + s / Q) (htime s hs)
          (d.forward s hs x) = e.forward s ⟨ha.le.trans hs.1, hs.2⟩ x) ∧
        (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
          d.pullbackInner s hs x v w =
            e.pullbackInner s ⟨ha.le.trans hs.1, hs.2⟩ x v w) ∧
        let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
        let j := terminalSourceNormal_terminalMap U p0
          (terminalSourceNormal_historyCylinder H U htime d) h0
        (∀ y : U, j y = y.val) ∧ Set.range (fun y : U => j y) = U := by
  have hsub : Icc (-tau) 0 ⊆ Icc a 0 :=
    fun _ hs => ⟨ha.le.trans hs.1, hs.2⟩
  let closed : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau) 0) U :=
    e.restrict hsub ordConnected_Icc (Subset.refl (U : Set (F.slice base).carrier))
  have htime (s : ℝ) (hs : s ∈ Icc (-tau) 0) :
      base + s / Q ∈ H.generalized.interval := by
    rw [H.interval_eq]
    apply W.interval_connected.out W.zero_mem (H.interval_eq ▸ hbase)
    exact ⟨F.time_domain_nonnegative
      (e.time_subset (mem_image_of_mem _ (hsub hs))),
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 e.scale_pos.le)⟩
  have hregular (s : ℝ) (hs : s ∈ Icc (-tau) 0) :
      closed.forward s hs '' (U : Set (F.slice base).carrier) ⊆
        m33RegularRegion F (base + s / Q) := by
    apply e.regular_image_of_earlier (hsub hs)
    exact ⟨a, ⟨le_rfl, (ha.trans (neg_neg_of_pos htau)).le⟩, ha.trans_le hs.1⟩
  obtain ⟨d, hmaps, hmetric⟩ := H.cylinders_from_surgery (F.slice base) base Q
    (Icc (-tau) 0) U U.isOpen htime closed hregular
  refine ⟨htime, d, hmaps, hmetric, ?_⟩
  let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
  let j := terminalSourceNormal_terminalMap U p0
    (terminalSourceNormal_historyCylinder H U htime d) h0
  have hterminal := terminalSourceNormal_history_terminal_map H U htime d p0 h0
  have hclock : base + 0 / Q = base := by simp only [zero_div, add_zero]
  have hidentity :
      (⟨base + 0 / Q, fun y : U =>
        H.history.forward (base + 0 / Q) (htime 0 h0) (d.forward 0 h0 y.val)⟩ :
          (t : ℝ) × (U → (F.slice t).carrier)) =
      ⟨base, (Subtype.val : U → (F.slice base).carrier)⟩ := by
    apply Sigma.ext hclock
    apply Function.hfunext rfl
    intro y z hyz
    cases hyz
    exact (heq_of_eq (hmaps 0 h0 y.val y.property)).trans
      (hbased (hsub h0) y.val y.property)
  have hwhole :
      (⟨base, fun y : U => j y⟩ : (t : ℝ) × (U → (F.slice t).carrier)) =
        ⟨base, (Subtype.val : U → (F.slice base).carrier)⟩ :=
    hterminal.trans hidentity
  have hfun : (fun y : U => j y) = Subtype.val := eq_of_heq (Sigma.mk.inj hwhole).2
  have hj (y : U) : j y = y.val := congrFun hfun y
  change (∀ y : U, j y = y.val) ∧ Set.range (fun y : U => j y) = U
  refine ⟨hj, ?_⟩
  apply Set.ext
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    change j z ∈ U
    rw [hj z]
    exact z.property
  · intro hy
    exact ⟨⟨y, hy⟩, hj ⟨y, hy⟩⟩

end PoincareMT.M47
