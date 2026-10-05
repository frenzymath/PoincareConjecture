import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinders
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceGeometry

/-!
# A disappearing cap has no regular history point at its top

Proposition 16.13 and Lemma 16.15, pp. 377-381. An actual history box
through the top surgery has all its nearby pre-surgery points inside
the retained pre-region. M44's disappearing alternative puts every
late cap point outside that same region. Their actual pre-identify
maps coincide, giving exclusion even from the cap trace's closure.
-/

set_option autoImplicit false
-- Actual history and cap points retain their dependent surgery slice fibers.
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M12
end PoincareMT.Proofs.M12
open PoincareMT.EpochExtension.Spacetime
local notation "GeneralizedFlowCarrierConclusion" => PoincareMT.GeneralizedFlowCarrierConclusionWithInterval

namespace PoincareMT.Proofs.M46

open PoincareMT.Proofs.M12

private theorem historyPoint_time_mem (G : GeneralizedRicciFlowData.{u}) (p : G.point) :
    p.1 ∈ G.interval := by
  obtain ⟨b, hb, x, hx⟩ := G.box_covers p.1 p.2
  exact m33BoxIntervalSubset G b hb

/-- The literal physical surgery-flow point of one selected regular
history point. Source: Proposition 14.12, p. 350. -/
def historyPhysicalPoint {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    (H : M33RegularHistoryRealization G F) (p : G.point) :
    Σ t, (F.slice t).carrier :=
  ⟨p.1, H.forward p.1 (historyPoint_time_mem G p) p.2⟩

private theorem preIdentify_congr {F : SurgeryFlowData.{u}}
    {t : ℝ} (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier]
    {p z : Σ s, (F.slice s).carrier} (hpz : p = z)
    (hp : p.1 ∈ Ico (F.event t hT).tMinus t)
    (hz : z.1 ∈ Ico (F.event t hT).tMinus t) :
    ((F.event t hT).pre_identify ⟨p.1, hp⟩).symm p.2 =
      ((F.event t hT).pre_identify ⟨z.1, hz⟩).symm z.2 := by
  cases hpz
  rfl

/-- No actual regular history point at a disappearing cap's top lies
in the closure of that cap's physical trace. Source: Proposition 16.13
and Lemma 16.15, pp. 377-381. -/
theorem disappearingCap_trace_closure_excludes_top
    {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
    (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas G))
    (H : M33RegularHistoryRealization G F)
    {origin scale tPlus : ℝ} {I : Set ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    (hdisappears : SurgeryBallDisappearsAt F e tPlus)
    (hbefore : ∀ s ∈ I, origin + s / scale < tPlus)
    (p : R.spacetime.Point) (hp : R.spacetime.timeFunction p = tPlus) :
    p ∉ closure {z : R.spacetime.Point |
      ∃ (s : ℝ) (hs : s ∈ I) (x : (F.slice origin).carrier), x ∈ U ∧
        (⟨origin + s / scale, e.forward s hs x⟩ : Σ t, (F.slice t).carrier) =
          historyPhysicalPoint H z} := by
  let : ChartedSpace
      (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 3))) G.point :=
    R.spacetime.chartedSpace
  rcases p with ⟨t, y⟩
  change t = tPlus at hp
  subst t
  rcases hdisappears with hempty | ⟨hPlus, hn, _, s0, hs0, hcut⟩
  · let : IsEmpty (F.slice tPlus).carrier := hempty
    exact isEmptyElim (H.forward tPlus
      (historyPoint_time_mem G (⟨tPlus, y⟩ : G.point)) y)
  · let : Nonempty (F.slice tPlus).carrier := hn
    let event := F.event tPlus hPlus
    obtain ⟨b, htb, x, hxb⟩ := G.box_covers tPlus y
    let threshold := max event.tMinus (origin + s0 / scale)
    have hthreshold : threshold < tPlus :=
      max_lt event.tMinus_lt (hbefore s0 hs0)
    let V : Set R.spacetime.Point := range (originalBoxMap G R b) ∩
      R.spacetime.timeFunction ⁻¹' Ioi threshold
    have hVopen : IsOpen V := (G.box_openEmbedding b).isOpen_range.inter
      (isOpen_Ioi.preimage R.spacetime.time_smooth.continuous)
    have hVpoint : (⟨tPlus, y⟩ : R.spacetime.Point) ∈ V := by
      refine ⟨?_, hthreshold⟩
      exact ⟨(⟨tPlus, htb⟩, x), congrArg (fun z => (⟨tPlus, z⟩ : G.point)) hxb⟩
    intro hclosure
    obtain ⟨z, ⟨hzbox, hztime⟩, s, hs, v, hv, hpoint⟩ :=
      mem_closure_iff_nhds.mp hclosure V (hVopen.mem_nhds hVpoint)
    obtain ⟨w, hw⟩ := hzbox
    rw [← hw] at hztime hpoint
    have hclock : origin + s / scale = w.1.val := congrArg Sigma.fst hpoint
    change threshold < w.1.val at hztime
    have hlate : threshold < origin + s / scale := by rwa [hclock]
    have hs0le : s0 ≤ s := by
      have h := (le_max_right event.tMinus (origin + s0 / scale)).trans_lt hlate
      exact ((div_lt_div_iff_of_pos_right e.scale_pos).mp (lt_of_add_lt_add_left h)).le
    have hpre : origin + s / scale ∈ Ico event.tMinus tPlus :=
      ⟨((le_max_left _ _).trans_lt hlate).le, hbefore s hs⟩
    have hprew : w.1.val ∈ Ico event.tMinus tPlus := hclock ▸ hpre
    have hnot := hcut s hs hs0le v hv hpre
    have hretained := H.pre_retained_at_surgery b tPlus htb hPlus w.1.val w.1.property
      hprew w.2
    have heq := preIdentify_congr hPlus hpoint hpre hprew
    change (event.pre_identify ⟨origin + s / scale, hpre⟩).symm (e.forward s hs v) =
      (event.pre_identify ⟨w.1.val, hprew⟩).symm
        (H.forward w.1.val (m33BoxIntervalSubset G b w.1.property)
          ((G.box b).forward w.1.val w.1.property w.2)) at heq
    exact hnot (heq.symm ▸ hretained)

end PoincareMT.Proofs.M46
