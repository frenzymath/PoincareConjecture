import PoincareLib.Topology.Manifold.Surgery.Event.Monodromy.MonodromyTrivialization
import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Topology

/-!
# The compact connected smooth sphere-bundle summand

Lift the literal monodromy quotient to the required universe through its
actual down homeomorphism. Its topology and pushed atlas give the carrier,
and the same local coordinates give the frozen SurgerySphereBundle fields.
The monodromy is an arbitrary supplied sphere diffeomorphism.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold

/-- Lift precisely the quotient atlas along the literal down homeomorphism. -/
@[instance_reducible]
noncomputable def monodromyLiftChartedSpace :
    ChartedSpace StandardCapSpace (ULift.{u} (MonodromyQuotient phi)) where
  atlas := Set.range (fun p : MonodromyQuotient phi =>
    (Homeomorph.toOpenPartialHomeomorph
      (Homeomorph.ulift : ULift.{u} (MonodromyQuotient phi) ≃ₜ MonodromyQuotient phi)).trans
        (chartAt StandardCapSpace p))
  chartAt p := (Homeomorph.toOpenPartialHomeomorph
    (Homeomorph.ulift : ULift.{u} (MonodromyQuotient phi) ≃ₜ MonodromyQuotient phi)).trans
      (chartAt StandardCapSpace p.down)
  mem_chart_source p := by
    refine ⟨Set.mem_univ p, ?_⟩
    change p.down ∈ (chartAt StandardCapSpace p.down).source
    exact mem_chart_source _ p.down
  chart_mem_atlas p := ⟨p.down, rfl⟩

/-- The lifted transitions are exactly the established smooth quotient transitions. -/
theorem monodromy_lift_isManifold :
    letI := monodromyLiftChartedSpace.{u} phi
    IsManifold (𝓡 3) ∞ (ULift.{u} (MonodromyQuotient phi)) := by
  let := monodromyLiftChartedSpace.{u} phi
  apply isManifold_of_contDiffOn (𝓡 3) ∞ (ULift.{u} (MonodromyQuotient phi))
  intro e e' he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨p', rfl⟩ := he'
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (chartAt StandardCapSpace p')
      (chartAt StandardCapSpace p').source := contMDiffOn_chart
  have hcs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (chartAt StandardCapSpace p).symm
      (chartAt StandardCapSpace p).target := contMDiffOn_chart_symm
  simpa only [mfld_simps, Set.preimage_preimage, Function.comp_def,
    Homeomorph.apply_symm_apply] using (hc.comp' hcs).contDiffOn

attribute [local instance] monodromyLiftChartedSpace monodromy_lift_isManifold

/-- The actual down map is smooth in the lifted quotient atlas. -/
theorem monodromy_down_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (ULift.down : ULift.{u} (MonodromyQuotient phi) → MonodromyQuotient phi) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftDown.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)

/-- The actual up map has the same quotient coordinates and is smooth. -/
theorem monodromy_up_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (ULift.up : MonodromyQuotient phi → ULift.{u} (MonodromyQuotient phi)) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftUp.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)

/-- Universe lifting preserves the exact smooth monodromy quotient. -/
noncomputable def monodromyLiftDiffeomorph :
    (ULift.{u} (MonodromyQuotient phi)) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ MonodromyQuotient phi where
  toEquiv := Equiv.ulift
  contMDiff_toFun := monodromy_down_contMDiff phi
  contMDiff_invFun := monodromy_up_contMDiff phi

/-- The lifted compact quotient with its literal Borel space and smooth atlas. -/
noncomputable def monodromyCarrier : GeneralizedSliceCarrier.{u} := by
  letI : MeasurableSpace (ULift.{u} (MonodromyQuotient phi)) :=
    borel (ULift.{u} (MonodromyQuotient phi))
  exact {
    carrier := ULift.{u} (MonodromyQuotient phi)
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := ⟨rfl⟩
    chartedSpace := monodromyLiftChartedSpace phi
    isManifold := monodromy_lift_isManifold phi
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := Homeomorph.ulift.secondCountableTopology }

/-- The literal lifted summand is compact, by the quotient's compact annulus. -/
theorem monodromyCarrier_compact :
    IsCompact (Set.univ : Set (monodromyCarrier.{u} phi).carrier) := by
  let : CompactSpace (ULift.{u} (MonodromyQuotient phi)) :=
    Homeomorph.ulift.symm.surjective.compactSpace Homeomorph.ulift.symm.continuous
  change IsCompact (Set.univ : Set (ULift.{u} (MonodromyQuotient phi)))
  exact isCompact_univ

/-- The literal lifted summand is connected, by its connected covering puncture. -/
theorem monodromyCarrier_connected :
    IsConnected (Set.univ : Set (monodromyCarrier.{u} phi).carrier) := by
  let : ConnectedSpace (ULift.{u} (MonodromyQuotient phi)) :=
    Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
  change IsConnected (Set.univ : Set (ULift.{u} (MonodromyQuotient phi)))
  exact isConnected_univ

/-- The actual monodromy quotient has a smooth sphere-bundle structure with
the specified angle projection and the previously constructed local charts. -/
noncomputable def monodromySphereBundle : SurgerySphereBundle (monodromyCarrier.{u} phi) where
  projection q := monodromyProjection phi q.down
  projection_continuous := (monodromyProjection_continuous phi).comp continuous_uliftDown
  projection_surjective := by
    intro b
    obtain ⟨q, hq⟩ := monodromyProjection_surjective phi b
    exact ⟨ULift.up q, hq⟩
  projection_smooth := (monodromyProjection_smooth phi).comp (monodromy_down_contMDiff phi)
  local_trivialization := by
    intro b
    refine ⟨circleLiftArc b, circleLiftArc_open b, circleLiftArc_self b,
      (fun q => monodromyLocalCoordinates phi b q.down),
      (fun p => ULift.up (monodromyLocalInverse phi b p)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨Set.mem_univ _, hq⟩
      · intro hp
        refine ⟨ULift.up (monodromyLocalInverse phi b p), ?_,
          monodromyLocalCoordinates_right_inv phi b p⟩
        change monodromyProjection phi (monodromyLocalInverse phi b p) ∈ circleLiftArc b
        rw [monodromyLocalInverse_projection]
        exact hp.2
    · intro q _
      apply ULift.ext
      exact monodromyLocalCoordinates_left_inv phi b q.down
    · intro p _
      exact monodromyLocalCoordinates_right_inv phi b p
    · exact (monodromyLocalCoordinates_smooth phi b).comp
        (monodromy_down_contMDiff phi).contMDiffOn (fun _ hq => hq)
    · exact (monodromy_up_contMDiff phi).comp_contMDiffOn
        (monodromyLocalInverse_smooth phi b)
    · intro q _
      rfl

end PoincareMT.M38
