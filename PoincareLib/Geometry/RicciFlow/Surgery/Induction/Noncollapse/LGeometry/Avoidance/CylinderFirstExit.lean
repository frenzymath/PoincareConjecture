import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.CapEntry.CylinderRelativeImage
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Local.ContinuousFirstExit

/-!
# First exit from an included tested cylinder

Lemma 16.15, pp. 379-381. The actual closed cylinder image need not
be open in the whole history at its terminal clock. It is open along
every continuous curve whose clocks remain in the physical interval.
This supplies the first exit without extending the cylinder in time.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT.Proofs.M12
end PoincareMT.Proofs.M12
open PoincareMT.EpochExtension.Spacetime
local notation "GeneralizedFlowCarrierConclusion" => PoincareMT.GeneralizedFlowCarrierConclusionWithInterval

namespace PoincareMT.Proofs.M46

open PoincareMT.Proofs.M12

/-- Relative openness in the actual physical clock interval gives
openness of capture on any continuous parameter space with included
clocks. Source: Lemma 16.15, pp. 379-381. -/
theorem rawCylinder_preimage_isOpen
    {F : GeneralizedRicciFlowData.{u}}
    (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    {A : Type v} [TopologicalSpace A] (gamma : A → R.spacetime.Point)
    (hgamma : Continuous gamma)
    (hclock : ∀ t, R.spacetime.timeFunction (gamma t) ∈
      (cylinderPhysicalInterval origin scale e.scale_pos J).domain) :
    IsOpen (gamma ⁻¹' range (rawCylinderMap R e)) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro t ⟨p, hp⟩
  have hnear := rawCylinder_range_mem_nhdsWithin_clock R e hI p
  rw [hp] at hnear
  have htend : Tendsto gamma (𝓝 t)
      (𝓝[R.spacetime.timeFunction ⁻¹'
        (cylinderPhysicalInterval origin scale e.scale_pos J).domain] (gamma t)) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hgamma.continuousAt, Eventually.of_forall hclock⟩
  exact htend hnear

/-- First exit needs openness only along the closed parameter interval,
not an ambient open image of the tracked cylinder. Source: Lemma 16.15,
pp. 379-381. -/
theorem exists_first_exit_of_relative_preimage
    {X : Type v} [TopologicalSpace X] {gamma : ℝ → X} {a b : ℝ}
    (hgamma : ContinuousOn gamma (Icc a b)) {O : Set X}
    (hrelative : IsOpen {t : Icc a b | gamma t.val ∈ O})
    (ha : gamma a ∈ O) (hleave : ∃ s ∈ Icc a b, gamma s ∉ O) :
    ∃ c ∈ Ioc a b, gamma c ∉ O ∧ MapsTo gamma (Ico a c) O ∧
      MapsTo gamma (Icc a c) (closure O) := by
  obtain ⟨V, hV, hVeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hrelative
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : t ∈ V ↔ gamma t ∈ O := by
    exact iff_of_eq (congrArg (fun S : Set (Icc a b) => (⟨t, ht⟩ : Icc a b) ∈ S) hVeq)
  obtain ⟨s, hs, hsout⟩ := hleave
  have hab : a ≤ b := hs.1.trans hs.2
  obtain ⟨c, hc, hcout, hinside, _⟩ := M14.exists_first_exit_of_continuousOn
    (continuousOn_id : ContinuousOn (id : ℝ → ℝ) (Icc a b)) hV
    ((hmem a ⟨le_rfl, hab⟩).mpr ha) ⟨s, hs, fun h => hsout ((hmem s hs).mp h)⟩
  have hactual : MapsTo gamma (Ico a c) O := by
    intro t ht
    exact (hmem t ⟨ht.1, ht.2.le.trans hc.2⟩).mp (hinside ht)
  refine ⟨c, hc, fun h => hcout ((hmem c ⟨hc.1.le, hc.2⟩).mpr h), hactual, ?_⟩
  have hcont : ContinuousOn gamma (closure (Ico a c)) := by
    rw [closure_Ico hc.1.ne]
    exact hgamma.mono (Icc_subset_Icc le_rfl hc.2)
  have hclosure := hactual.closure_of_continuousOn hcont
  simpa only [closure_Ico hc.1.ne] using hclosure

end PoincareMT.Proofs.M46
