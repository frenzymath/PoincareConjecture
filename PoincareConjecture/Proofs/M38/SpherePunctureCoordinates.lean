import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Proofs.M38.ThreeSphereConnection

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M38

section Lift

variable (X : Type v) [TopologicalSpace X] [ChartedSpace StandardCapSpace X]

@[instance_reducible]
noncomputable def threeManifoldLiftChartedSpace :
    ChartedSpace StandardCapSpace (ULift.{u} X) where
  atlas := Set.range (fun p : X =>
    (Homeomorph.toOpenPartialHomeomorph
      (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans (chartAt StandardCapSpace p))
  chartAt p := (Homeomorph.toOpenPartialHomeomorph
    (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans (chartAt StandardCapSpace p.down)
  mem_chart_source p := by
    refine ⟨Set.mem_univ p, ?_⟩
    change p.down ∈ (chartAt StandardCapSpace p.down).source
    exact mem_chart_source _ p.down
  chart_mem_atlas p := ⟨p.down, rfl⟩

variable [IsManifold (𝓡 3) ∞ X]

theorem threeManifold_lift_isManifold :
    letI : ChartedSpace StandardCapSpace (ULift.{u} X) := threeManifoldLiftChartedSpace X
    IsManifold (𝓡 3) ∞ (ULift.{u} X) := by
  letI : ChartedSpace StandardCapSpace (ULift.{u} X) := threeManifoldLiftChartedSpace X
  apply isManifold_of_contDiffOn (𝓡 3) ∞ (ULift.{u} X)
  intro e e' he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨p', rfl⟩ := he'
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (chartAt StandardCapSpace p')
      (chartAt StandardCapSpace p').source := contMDiffOn_chart
  have hcs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (chartAt StandardCapSpace p).symm
      (chartAt StandardCapSpace p).target := contMDiffOn_chart_symm
  simpa only [mfld_simps, Set.preimage_preimage, Function.comp_def,
    Homeomorph.apply_symm_apply] using (hc.comp' hcs).contDiffOn

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

theorem threeManifold_down_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (ULift.down : ULift.{u} X → X) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftDown.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)

theorem threeManifold_up_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (ULift.up : X → ULift.{u} X) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftUp.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)

end Lift

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

noncomputable def sphereCarrier : GeneralizedSliceCarrier.{u} := by
  letI : MeasurableSpace (ULift.{u} UnitThreeSphere) := borel (ULift.{u} UnitThreeSphere)
  exact {
    carrier := ULift.{u} UnitThreeSphere
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := ⟨rfl⟩
    chartedSpace := threeManifoldLiftChartedSpace UnitThreeSphere
    isManifold := threeManifold_lift_isManifold UnitThreeSphere
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := Homeomorph.ulift.secondCountableTopology }

noncomputable def euclideanCarrier : GeneralizedSliceCarrier.{u} := by
  letI : MeasurableSpace (ULift.{u} StandardCapSpace) := borel (ULift.{u} StandardCapSpace)
  exact {
    carrier := ULift.{u} StandardCapSpace
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := ⟨rfl⟩
    chartedSpace := threeManifoldLiftChartedSpace StandardCapSpace
    isManifold := threeManifold_lift_isManifold StandardCapSpace
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := Homeomorph.ulift.secondCountableTopology }

theorem threeSphereStereo_smooth (p : UnitThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (stereographic' 3 p) ({p}ᶜ : Set UnitThreeSphere) := by
  have hatlas : stereographic' 3 p ∈ atlas StandardCapSpace UnitThreeSphere := ⟨p, rfl⟩
  have hmax : stereographic' 3 p ∈ IsManifold.maximalAtlas (𝓡 3) ∞ UnitThreeSphere :=
    IsManifold.subset_maximalAtlas hatlas
  simpa only [stereographic'_source] using contMDiffOn_of_mem_maximalAtlas hmax

noncomputable def spherePunctureMap (p x : sphereCarrier.{u}.carrier) :
    euclideanCarrier.{u}.carrier := ULift.up (stereographic' 3 p.down x.down)

noncomputable def spherePunctureInverse (p : sphereCarrier.{u}.carrier)
    (y : euclideanCarrier.{u}.carrier) : sphereCarrier.{u}.carrier :=
  ULift.up (threeSphereStereoInverse p.down y.down)

theorem spherePunctureInverse_ne (p : sphereCarrier.{u}.carrier)
    (y : euclideanCarrier.{u}.carrier) : spherePunctureInverse p y ≠ p := by
  have hm : threeSphereStereoInverse p.down y.down ∈ (stereographic' 3 p.down).source :=
    (stereographic' 3 p.down).map_target (by simp)
  have hn : threeSphereStereoInverse p.down y.down ≠ p.down := by
    simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hm
  intro heq
  exact hn (congrArg ULift.down heq)

theorem spherePuncture_left_inverse (p : sphereCarrier.{u}.carrier) :
    Set.LeftInvOn (spherePunctureInverse p) (spherePunctureMap p)
      ({p}ᶜ : Set sphereCarrier.{u}.carrier) := by
  intro x hx
  have hn : x.down ≠ p.down := fun heq => hx (ULift.ext _ _ heq)
  apply ULift.ext
  change threeSphereStereoInverse p.down (stereographic' 3 p.down x.down) = x.down
  exact (stereographic' 3 p.down).left_inv (by
    simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hn)

theorem spherePuncture_right_inverse (p : sphereCarrier.{u}.carrier) :
    Set.LeftInvOn (spherePunctureMap p) (spherePunctureInverse p)
      (Set.univ : Set euclideanCarrier.{u}.carrier) := by
  intro y _
  apply ULift.ext
  change stereographic' 3 p.down (threeSphereStereoInverse p.down y.down) = y.down
  exact (stereographic' 3 p.down).right_inv (by simp)

theorem spherePunctureMap_image (p : sphereCarrier.{u}.carrier) :
    spherePunctureMap p '' ({p}ᶜ : Set sphereCarrier.{u}.carrier) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro y hy
  exact ⟨spherePunctureInverse p y, spherePunctureInverse_ne p y,
    spherePuncture_right_inverse p hy⟩

theorem spherePunctureInverse_image (p : sphereCarrier.{u}.carrier) :
    spherePunctureInverse p '' (Set.univ : Set euclideanCarrier.{u}.carrier) = {p}ᶜ := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, _, rfl⟩
    exact spherePunctureInverse_ne p y
  · intro x hx
    exact ⟨spherePunctureMap p x, Set.mem_univ _, spherePuncture_left_inverse p hx⟩

theorem spherePunctureMap_smooth (p : sphereCarrier.{u}.carrier) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (spherePunctureMap p)
      ({p}ᶜ : Set sphereCarrier.{u}.carrier) := by
  have hs := (threeSphereStereo_smooth p.down).comp
    (threeManifold_down_contMDiff UnitThreeSphere).contMDiffOn
    (show Set.MapsTo (ULift.down : sphereCarrier.{u}.carrier → UnitThreeSphere)
      {p}ᶜ {p.down}ᶜ from fun x hx heq => hx (ULift.ext _ _ heq))
  exact (threeManifold_up_contMDiff StandardCapSpace).comp_contMDiffOn hs

theorem spherePunctureInverse_smooth (p : sphereCarrier.{u}.carrier) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (spherePunctureInverse p) :=
  (threeManifold_up_contMDiff UnitThreeSphere).comp
    ((threeSphereStereoLocalDiffeomorph p.down).contMDiff.comp
      (threeManifold_down_contMDiff StandardCapSpace))

noncomputable def spherePunctureEquivalence (p : sphereCarrier.{u}.carrier) :
    SurgeryRegionEquivalence sphereCarrier.{u} euclideanCarrier.{u} {p}ᶜ Set.univ where
  map := spherePunctureMap p
  inverse := spherePunctureInverse p
  map_image := spherePunctureMap_image p
  inverse_image := spherePunctureInverse_image p
  left_inverse := spherePuncture_left_inverse p
  right_inverse := spherePuncture_right_inverse p
  map_smooth := spherePunctureMap_smooth p
  inverse_smooth := (spherePunctureInverse_smooth p).contMDiffOn

theorem spherePunctureEquivalence_map (p x : sphereCarrier.{u}.carrier) :
    (spherePunctureEquivalence p).map x = ULift.up (stereographic' 3 p.down x.down) := rfl

theorem spherePunctureEquivalence_inverse (p : sphereCarrier.{u}.carrier)
    (y : euclideanCarrier.{u}.carrier) :
    (spherePunctureEquivalence p).inverse y =
      ULift.up (threeSphereStereoInverse p.down y.down) := rfl

end PoincareConjecture.M38
