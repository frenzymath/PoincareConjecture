import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_InverseEnergy
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_SideAction
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_ActualPositiveAction
import PoincareConjecture.Proofs.M14.Sec6_1_InteriorDensity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Function
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)



theorem backwardPath_realizedKinetic_eq {T a b : ℝ} {x y : G.toLGeometry.Point}
    (p : M14BackwardPath G.toLGeometry T a b x y) {s : ℝ} (hs : s ∈ Ioo a b) :
    realizedHorizontalForm G.realization (p.curve s)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) p.curve s 1)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) p.curve s 1) =
      G.toLGeometry.spacetime.horizontalMetric.inner (p.curve s)
        (p.horizontal_velocity s) (p.horizontal_velocity s) := by
  change G.toLGeometry.spacetime.horizontalMetric.inner (p.curve s)
      (M14.projectedCurveVelocity G.toLGeometry p.curve s)
      (M14.projectedCurveVelocity G.toLGeometry p.curve s) = _
  rw [← M14.backwardPath_velocity_eq_projected p hs]




theorem exists_backwardCap_birthEnergy
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    (gBirth : RiemannianMetric 3 C.carrier) {mu : ℝ} (hmu : 0 < mu)
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (z : U)
      (v : TangentSpace (𝓡 3) z.val),
      scale * (mu * gBirth.inner z.val v v) ≤ e.pullbackInner s hs z.val v v)
    {T tau a b : ℝ} {x y : G.toLGeometry.Point}
    (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (ha : 0 < a) (hab : a < b) (hbtau : b ≤ tau)
    (himage : MapsTo p.curve (Ioo a b) (range (rawCylinderMap G.realization e))) :
    ∃ beta : ℝ → (G.realization.timeIntervals.interval
        (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U,
      EqOn (rawCylinderMap G.realization e ∘ beta) p.curve (Ioo a b) ∧
        ContinuousOn beta (Ioo a b) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun t => (beta t).2.val) (Ioo a b) ∧
        (∀ t ∈ Ioo a b, (beta t).1.val = G.realization.spacetime.timeFunction (p.curve t)) ∧
        (∀ t ∈ Ioo a b,
          mu * M08.referenceSpeedSq gBirth (fun r => (beta r).2.val) t ≤
            pathPositiveDensity p t) ∧
        IntervalIntegrable (M08.referenceSpeedSq gBirth (fun t => (beta t).2.val)) volume a b ∧
        mu * (∫ t in a..b, M08.referenceSpeedSq gBirth (fun r => (beta r).2.val) t) ≤
          ∫ t in a..b, pathPositiveDensity p t := by
  have hsub : Ioo a b ⊆ Ioo 0 tau := Ioo_subset_Ioo ha.le hbtau
  obtain ⟨beta, heq, hcont, hregular, hclock, henergy⟩ :=
    exists_rawCylinder_energy_lift G e hI gBirth mu hbound (nonempty_Ioo.mpr hab)
      isOpen_Ioo (p.curve_regular.mono hsub) himage
  have hpositive := pathPositiveDensity_tail_integrable hM12 p ha hab.le hbtau
  have hpoint : ∀ t ∈ Ioo a b,
      mu * M08.referenceSpeedSq gBirth (fun r => (beta r).2.val) t ≤
        pathPositiveDensity p t := by
    intro t ht
    apply ((henergy t ht).trans_eq (backwardPath_realizedKinetic_eq G p (hsub ht))).trans
    exact le_add_of_nonneg_left (le_max_right _ _)
  obtain ⟨hint, hboundEnergy⟩ := birthEnergy_integrable_of_action_bound gBirth hab.le hmu
    hregular (pathPositiveDensity p) hpositive hpoint
  exact ⟨beta, heq, hcont, hregular, hclock, hpoint, hint, hboundEnergy⟩

end PoincareConjecture.Proofs.M46
