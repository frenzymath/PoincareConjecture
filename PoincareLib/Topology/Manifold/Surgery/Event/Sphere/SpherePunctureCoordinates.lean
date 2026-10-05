import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Topology
import PoincareLib.Topology.Manifold.Surgery.Event.Three.ThreeSphereConnection

/-!
# Exact stereographic coordinates for the punctured three-sphere

The sphere and Euclidean carriers are literal universe lifts with their
existing atlases and Borel spaces. The supplied stereographic chart and
its existing inverse identify exactly the complement of its chosen pole
with the whole Euclidean carrier.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M38

section Lift

variable (X : Type v) [TopologicalSpace X] [ChartedSpace StandardCapSpace X]

/-- Lift the original three-dimensional atlas through the literal down homeomorphism. -/
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

/-- The lifted chart transitions are precisely the original smooth transitions. -/
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

/-- The literal down map is smooth in the lifted original atlas. -/
theorem threeManifold_down_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (ULift.down : ULift.{u} X → X) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftDown.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)

/-- The literal up map retains the same original chart coordinates. -/
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

/-- The literal lifted three-sphere with its existing stereographic atlas and Borel space. -/
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

/-- The literal lifted standard cap space with its original Euclidean atlas and Borel space. -/
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

/-- The actual stereographic chart is smooth on exactly the complement of its chosen pole. -/
theorem threeSphereStereo_smooth (p : UnitThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (stereographic' 3 p) ({p}ᶜ : Set UnitThreeSphere) := by
  have hatlas : stereographic' 3 p ∈ atlas StandardCapSpace UnitThreeSphere := ⟨p, rfl⟩
  have hmax : stereographic' 3 p ∈ IsManifold.maximalAtlas (𝓡 3) ∞ UnitThreeSphere :=
    IsManifold.subset_maximalAtlas hatlas
  simpa only [stereographic'_source] using contMDiffOn_of_mem_maximalAtlas hmax

/-- The total forward map is the original stereographic chart after literal universe lowering. -/
noncomputable def spherePunctureMap (p x : sphereCarrier.{u}.carrier) :
    euclideanCarrier.{u}.carrier := ULift.up (stereographic' 3 p.down x.down)

/-- The total inverse is the lift of the existing inverse stereographic projection. -/
noncomputable def spherePunctureInverse (p : sphereCarrier.{u}.carrier)
    (y : euclideanCarrier.{u}.carrier) : sphereCarrier.{u}.carrier :=
  ULift.up (threeSphereStereoInverse p.down y.down)

/-- Every actual inverse image avoids precisely the originally chosen pole. -/
theorem spherePunctureInverse_ne (p : sphereCarrier.{u}.carrier)
    (y : euclideanCarrier.{u}.carrier) : spherePunctureInverse p y ≠ p := by
  have hm : threeSphereStereoInverse p.down y.down ∈ (stereographic' 3 p.down).source :=
    (stereographic' 3 p.down).map_target (by simp)
  have hn : threeSphereStereoInverse p.down y.down ≠ p.down := by
    simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hm
  intro heq
  exact hn (congrArg ULift.down heq)

/-- The stored chart inverse recovers every point in the literal punctured sphere. -/
theorem spherePuncture_left_inverse (p : sphereCarrier.{u}.carrier) :
    Set.LeftInvOn (spherePunctureInverse p) (spherePunctureMap p)
      ({p}ᶜ : Set sphereCarrier.{u}.carrier) := by
  intro x hx
  have hn : x.down ≠ p.down := fun heq => hx (ULift.ext _ _ heq)
  apply ULift.ext
  change threeSphereStereoInverse p.down (stereographic' 3 p.down x.down) = x.down
  exact (stereographic' 3 p.down).left_inv (by
    simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hn)

/-- All Euclidean points lie in the original stereographic target, so the reverse law is global. -/
theorem spherePuncture_right_inverse (p : sphereCarrier.{u}.carrier) :
    Set.LeftInvOn (spherePunctureMap p) (spherePunctureInverse p)
      (Set.univ : Set euclideanCarrier.{u}.carrier) := by
  intro y _
  apply ULift.ext
  change stereographic' 3 p.down (threeSphereStereoInverse p.down y.down) = y.down
  exact (stereographic' 3 p.down).right_inv (by simp)

/-- The exact punctured-sphere image is the whole literal Euclidean carrier. -/
theorem spherePunctureMap_image (p : sphereCarrier.{u}.carrier) :
    spherePunctureMap p '' ({p}ᶜ : Set sphereCarrier.{u}.carrier) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro y hy
  exact ⟨spherePunctureInverse p y, spherePunctureInverse_ne p y,
    spherePuncture_right_inverse p hy⟩

/-- The actual inverse image is exactly the complement of the same marked pole. -/
theorem spherePunctureInverse_image (p : sphereCarrier.{u}.carrier) :
    spherePunctureInverse p '' (Set.univ : Set euclideanCarrier.{u}.carrier) = {p}ᶜ := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, _, rfl⟩
    exact spherePunctureInverse_ne p y
  · intro x hx
    exact ⟨spherePunctureMap p x, Set.mem_univ _, spherePuncture_left_inverse p hx⟩

/-- The lifted chart is smooth on its actual punctured source for the inherited atlases. -/
theorem spherePunctureMap_smooth (p : sphereCarrier.{u}.carrier) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (spherePunctureMap p)
      ({p}ᶜ : Set sphereCarrier.{u}.carrier) := by
  have hs := (threeSphereStereo_smooth p.down).comp
    (threeManifold_down_contMDiff UnitThreeSphere).contMDiffOn
    (show Set.MapsTo (ULift.down : sphereCarrier.{u}.carrier → UnitThreeSphere)
      {p}ᶜ {p.down}ᶜ from fun x hx heq => hx (ULift.ext _ _ heq))
  exact (threeManifold_up_contMDiff StandardCapSpace).comp_contMDiffOn hs

/-- The lifted inverse is smooth on the whole Euclidean carrier, using the existing inverse chart. -/
theorem spherePunctureInverse_smooth (p : sphereCarrier.{u}.carrier) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (spherePunctureInverse p) :=
  (threeManifold_up_contMDiff UnitThreeSphere).comp
    ((threeSphereStereoLocalDiffeomorph p.down).contMDiff.comp
      (threeManifold_down_contMDiff StandardCapSpace))

/-- The literal punctured three-sphere and full Euclidean carriers are
smoothly identified by the same stereographic map and inverse. This is
the puncture comparison used in the ball-complement reconstruction for
Morgan--Tian Proposition 15.3, pp. 357-358. -/
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

/-- Packaging the region equivalence preserves the exact total stereographic formula. -/
theorem spherePunctureEquivalence_map (p x : sphereCarrier.{u}.carrier) :
    (spherePunctureEquivalence p).map x = ULift.up (stereographic' 3 p.down x.down) := rfl

/-- The packaged inverse retains the exact existing inverse stereographic map. -/
theorem spherePunctureEquivalence_inverse (p : sphereCarrier.{u}.carrier)
    (y : euclideanCarrier.{u}.carrier) :
    (spherePunctureEquivalence p).inverse y =
      ULift.up (threeSphereStereoInverse p.down y.down) := rfl

end PoincareMT.M38
