import PoincareConjecture.Proofs.M38.MonodromyTrivialization
import PoincareConjecture.Definitions.Ch15.SurgeryTopology










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold


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


theorem monodromy_down_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (ULift.down : ULift.{u} (MonodromyQuotient phi) → MonodromyQuotient phi) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftDown.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)


theorem monodromy_up_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (ULift.up : MonodromyQuotient phi → ULift.{u} (MonodromyQuotient phi)) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftUp.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)


noncomputable def monodromyLiftDiffeomorph :
    (ULift.{u} (MonodromyQuotient phi)) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ MonodromyQuotient phi where
  toEquiv := Equiv.ulift
  contMDiff_toFun := monodromy_down_contMDiff phi
  contMDiff_invFun := monodromy_up_contMDiff phi


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


theorem monodromyCarrier_compact :
    IsCompact (Set.univ : Set (monodromyCarrier.{u} phi).carrier) := by
  let : CompactSpace (ULift.{u} (MonodromyQuotient phi)) :=
    Homeomorph.ulift.symm.surjective.compactSpace Homeomorph.ulift.symm.continuous
  change IsCompact (Set.univ : Set (ULift.{u} (MonodromyQuotient phi)))
  exact isCompact_univ


theorem monodromyCarrier_connected :
    IsConnected (Set.univ : Set (monodromyCarrier.{u} phi).carrier) := by
  let : ConnectedSpace (ULift.{u} (MonodromyQuotient phi)) :=
    Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
  change IsConnected (Set.univ : Set (ULift.{u} (MonodromyQuotient phi)))
  exact isConnected_univ



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

end PoincareConjecture.M38
