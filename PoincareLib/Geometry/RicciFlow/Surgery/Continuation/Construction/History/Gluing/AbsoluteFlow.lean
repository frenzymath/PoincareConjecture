import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Gluing.SmoothFlow
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Gluing.RetainedLimit
import PoincareLib.Geometry.RicciFlow.TimeTranslation

/-!
# Smooth ordinary flow across an old surgery

Translate the existing smooth-gluing theorem to the absolute event time and
apply it to the actual continuing pre- and post-flows. Both metric families
are preserved on their respective intervals.
Source: Morgan--Tian, Lemma 14.11 and Proposition 14.12, pp. 349-350.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- Compact-uniform metric-jet convergence glues the two ordinary flows on
their original absolute time intervals. -/
theorem SurgeryMetricLimitOn.exists_absolute_gluing
    {S : GeneralizedSliceCarrier.{u}} {a b c : ℝ}
    {F : RicciFlow 3 S.carrier (Ico a b)} {G : RicciFlow 3 S.carrier (Ico b c)}
    (h : SurgeryMetricLimitOn S S F.metric (G.metric b) id univ b)
    (hab : a < b) (hbc : b < c) :
    ∃ H : RicciFlow 3 S.carrier (Ico a c),
      EqOn F.metric H.metric (Ico a b) ∧ EqOn G.metric H.metric (Ico b c) := by
  let F₀ : RicciFlow 3 S.carrier (Ico 0 (b - a)) :=
    F.translate a
      (by rintro _ ⟨t, ht, rfl⟩; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      ordConnected_Ico
      ⟨0, ⟨le_rfl, by linarith⟩, (b - a) / 2,
        ⟨by linarith, by linarith⟩, by linarith⟩
  let G₀ : RicciFlow 3 S.carrier (Ico (b - a) ((b - a) + (c - b))) :=
    G.translate a
      (by rintro _ ⟨t, ht, rfl⟩; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      ordConnected_Ico
      ⟨b - a, ⟨le_rfl, by linarith⟩, (b - a) + (c - b) / 2,
        ⟨by linarith, by linarith⟩, by linarith⟩
  have h₀ : SurgeryMetricLimitOn S S F₀.metric (G₀.metric (b - a)) id univ (b - a) := by
    change SurgeryMetricLimitOn S S (fun t => F.metric (t + a))
      (G.metric ((b - a) + a)) id univ (b - a)
    rw [sub_add_cancel]
    exact h.translateTime a
  obtain ⟨H₀, hF, hG⟩ := h₀.exists_zero_start_gluing (sub_pos.mpr hab) (sub_pos.mpr hbc)
  let H : RicciFlow 3 S.carrier (Ico a c) :=
    H₀.translate (-a)
      (by rintro _ ⟨t, ht, rfl⟩; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      ordConnected_Ico
      ⟨a, ⟨le_rfl, hab.trans hbc⟩, (a + c) / 2,
        ⟨by linarith, by linarith⟩, by linarith⟩
  refine ⟨H, ?_, ?_⟩
  · intro t ht
    have he := hF (show t + -a ∈ Ico 0 (b - a) from
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    change F.metric ((t + -a) + a) = H₀.metric (t + -a) at he
    change F.metric t = H₀.metric (t + -a)
    simpa only [neg_add_cancel_right] using he
  · intro t ht
    have he := hG (show t + -a ∈ Ico (b - a) ((b - a) + (c - b)) from
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    change G.metric ((t + -a) + a) = H₀.metric (t + -a) at he
    change G.metric t = H₀.metric (t + -a)
    simpa only [neg_add_cancel_right] using he

namespace SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {S : ℝ → GeneralizedSliceCarrier.{u}}
  {g : ∀ t, RiemannianMetric 3 (S t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P S g T)

/-- The old surgery data construct a smooth flow across the event on its
continuing interior, agreeing with the actual pre- and post-metrics. -/
theorem exists_continuing_flow {b : ℝ} (hb : T < b)
    (F : RicciFlow 3 (S T).carrier (Ico T b)) (hF : F.metric T = g T) :
    ∃ H : RicciFlow 3
      ((S E.tMinus).openSubset (SurgeryRegionEquivalence.sourceInterior (U := E.retained_pre))).carrier
      (Ico E.tMinus b),
      EqOn E.continuingPreFlow.metric H.metric (Ico E.tMinus T) ∧
      EqOn (E.continuingPostFlow F).metric H.metric (Ico T b) := by
  exact (E.continuing_metric_limit F hF).exists_absolute_gluing E.tMinus_lt hb

end SurgeryEventData

end PoincareMT
