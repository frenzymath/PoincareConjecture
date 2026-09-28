import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_CylinderEnergy
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Interval.RealTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

theorem rawCylinder_lift_time_contMDiffOn
    {F : GeneralizedRicciFlowData.{u}}
    (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
    {K : SpacetimeInterval} {B : Set ℝ}
    {gamma : ℝ → R.spacetime.Point}
    (theta : ℝ → (R.timeIntervals.interval K).Point)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 gamma B)
    (hclock : ∀ t ∈ B, (theta t).val = R.spacetime.timeFunction (gamma t)) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) 1 theta B := by
  let : ChartedSpace
      (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 3))) F.point :=
    R.spacetime.chartedSpace
  let T := R.timeIntervals.interval K
  have htime : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (R.spacetime.timeFunction ∘ gamma) B :=
    (R.spacetime.time_smooth.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp_contMDiffOn hgamma
  have hmaps : MapsTo (R.spacetime.timeFunction ∘ gamma) B K.domain := by
    intro t ht
    change R.spacetime.timeFunction (gamma t) ∈ K.domain
    rw [← hclock t ht]
    exact (theta t).property
  have hparam := (T.realParam_smoothOn.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp htime hmaps
  apply hparam.congr
  intro t ht
  apply Subtype.ext
  change (theta t).val = (T.realParam (R.spacetime.timeFunction (gamma t))).val
  exact (hclock t ht).trans (T.realParam_val (hmaps ht)).symm

theorem exists_rawCylinder_energy_lift
    {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
    {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C a q J.domain U)
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)
    (gBirth : RiemannianMetric 3 C.carrier) (mu : ℝ)
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (x : U)
      (v : TangentSpace (𝓡 3) x.val),
      q * (mu * gBirth.inner x.val v v) ≤ e.pullbackInner s hs x.val v v)
    {gamma : ℝ → G.realization.spacetime.Point} {B : Set ℝ}
    (hB : B.Nonempty) (hopen : IsOpen B)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 gamma B)
    (himage : MapsTo gamma B (range (rawCylinderMap G.realization e))) :
    ∃ beta : ℝ → (G.realization.timeIntervals.interval
        (cylinderPhysicalInterval a q e.scale_pos J)).Point × U,
      EqOn (rawCylinderMap G.realization e ∘ beta) gamma B ∧ ContinuousOn beta B ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun t => (beta t).2.val) B ∧
          (∀ t ∈ B, (beta t).1.val = G.realization.spacetime.timeFunction (gamma t)) ∧
          ∀ t ∈ B, mu * M08.referenceSpeedSq gBirth (fun r => (beta r).2.val) t ≤
            realizedHorizontalForm G.realization (gamma t)
              (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) gamma t 1)
              (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) gamma t 1) := by
  obtain ⟨beta, heq, hcont, hspatial, hclock⟩ :=
    exists_rawCylinder_lift G.realization e hI hB hgamma himage
  have htime := rawCylinder_lift_time_contMDiffOn G.realization
    (fun t => (beta t).1) hgamma hclock
  have hz : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun t => (beta t).2) B := by
    intro t ht
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(ℝ, ℝ) (𝓡 3) 1) (fun t => (beta t).2) B t).mp
        (hspatial t ht)
  refine ⟨beta, heq, hcont, hspatial, hclock, ?_⟩
  intro t ht
  have henergy := rawCylinder_birthEnergy_lower G e hI gBirth mu hbound
    (fun r => (beta r).1) (fun r => (beta r).2)
    (((htime t ht).contMDiffAt (hopen.mem_nhds ht)).mdifferentiableAt (by simp))
    (((hz t ht).contMDiffAt (hopen.mem_nhds ht)).mdifferentiableAt (by simp))
  have hpath : (rawCylinderMap G.realization e ∘ beta) =ᶠ[𝓝 t] gamma := by
    filter_upwards [hopen.mem_nhds ht] with r hr
    exact heq hr
  have hsame := realizedHorizontalEnergy_congr G hpath
  exact henergy.trans_eq hsame

end PoincareConjecture.Proofs.M46
