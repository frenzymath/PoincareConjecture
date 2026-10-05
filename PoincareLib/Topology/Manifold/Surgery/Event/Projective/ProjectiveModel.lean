import PoincareLib.Topology.Manifold.Surgery.Event.Projective.ProjectiveAtlas
import PoincareLib.Topology.Manifold.Surgery.Event.Projective.ProjectiveCurvature

/-!
# The literal positive-curvature projective summand

The actual smooth antipodal quotient is lifted to the required universe
without changing its atlas. The previously constructed descended metric
and connection give a positive spaceform on this same carrier.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

attribute [local instance] projectiveChartedSpace projective_isManifold

/-- The literal quotient is locally diffeomorphic, with the same inverse
sheets used to construct its smooth atlas. -/
theorem projective_quotient_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) := by
  intro x
  let s := projective_quotient_localHomeomorph.localInverseAt x
  refine ⟨{
    toPartialEquiv := s.symm.toPartialEquiv
    open_source := s.open_target
    open_target := s.open_source
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := projective_sheet_contMDiffOn x }, ?_, ?_⟩
  · simpa only [s, OpenPartialHomeomorph.coe_toPartialEquiv,
      OpenPartialHomeomorph.symm_source,
      projective_quotient_localHomeomorph.localInverseAt_symm]
      using projective_quotient_contMDiff.contMDiffOn
        (s := (projective_quotient_localHomeomorph.localInverseAt x).target)
  · exact projective_quotient_localHomeomorph.self_mem_localInverseAt_target
  · intro y _
    exact (congrFun (projective_quotient_localHomeomorph.localInverseAt_symm x) y).symm

/-- The standard cover uses the literal quotient, not an unspecified smooth
model homeomorphic to projective space. -/
noncomputable def literalProjectiveCover : StandardProjectiveSmoothCover RealProjectiveThree where
  cover := Quotient.mk'
  surjective := Quotient.mk_surjective
  fibers := fun _ _ => Quotient.eq
  local_diffeomorph := projective_quotient_localDiffeomorph

/-- Lift the chosen projective atlas through the literal down homeomorphism. -/
@[instance_reducible]
noncomputable def projectiveLiftChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} RealProjectiveThree) where
  atlas := Set.range (fun p : RealProjectiveThree =>
    (Homeomorph.toOpenPartialHomeomorph
      (Homeomorph.ulift : ULift.{u} RealProjectiveThree ≃ₜ RealProjectiveThree)).trans
        (chartAt (EuclideanSpace ℝ (Fin 3)) p))
  chartAt p := (Homeomorph.toOpenPartialHomeomorph
    (Homeomorph.ulift : ULift.{u} RealProjectiveThree ≃ₜ RealProjectiveThree)).trans
      (chartAt (EuclideanSpace ℝ (Fin 3)) p.down)
  mem_chart_source p := by
    refine ⟨Set.mem_univ p, ?_⟩
    change p.down ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) p.down).source
    exact mem_chart_source _ p.down
  chart_mem_atlas p := ⟨p.down, rfl⟩

/-- Lifted chart transitions are the original smooth projective transitions. -/
theorem projective_lift_isManifold :
    letI := projectiveLiftChartedSpace.{u}
    IsManifold (𝓡 3) ∞ (ULift.{u} RealProjectiveThree) := by
  letI := projectiveLiftChartedSpace.{u}
  apply isManifold_of_contDiffOn (𝓡 3) ∞ (ULift.{u} RealProjectiveThree)
  intro e e' he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨p', rfl⟩ := he'
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (chartAt (EuclideanSpace ℝ (Fin 3)) p')
      (chartAt (EuclideanSpace ℝ (Fin 3)) p').source := contMDiffOn_chart
  have hcs : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (chartAt (EuclideanSpace ℝ (Fin 3)) p).symm
      (chartAt (EuclideanSpace ℝ (Fin 3)) p).target := contMDiffOn_chart_symm
  simpa only [mfld_simps, Set.preimage_preimage, Function.comp_def,
    Homeomorph.apply_symm_apply] using (hc.comp' hcs).contDiffOn

attribute [local instance] projectiveLiftChartedSpace projective_lift_isManifold

/-- The literal down map is smooth in the lifted atlas. -/
theorem projective_down_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (ULift.down : ULift.{u} RealProjectiveThree → RealProjectiveThree) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftDown.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)

/-- The literal up map has the same coordinates and is smooth. -/
theorem projective_up_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (ULift.up : RealProjectiveThree → ULift.{u} RealProjectiveThree) := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_uliftUp.continuousAt, ?_⟩
  exact contMDiffAt_extChartAt (I := 𝓡 3) (x := p)

/-- Universe lifting is a diffeomorphism for this exact atlas. -/
noncomputable def projectiveLiftDiffeomorph :
    (ULift.{u} RealProjectiveThree) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ RealProjectiveThree where
  toEquiv := Equiv.ulift
  contMDiff_toFun := projective_down_contMDiff
  contMDiff_invFun := projective_up_contMDiff

/-- The lifted cover is exactly the lift of the literal quotient projection. -/
noncomputable def liftedProjectiveCover :
    StandardProjectiveSmoothCover (ULift.{u} RealProjectiveThree) where
  cover := fun x => ULift.up (Quotient.mk' x)
  surjective := by
    intro p
    obtain ⟨x, hx⟩ := Quotient.mk_surjective p.down
    refine ⟨x, ?_⟩
    apply ULift.ext
    exact hx
  fibers := by
    intro x y
    change ULift.up (Quotient.mk' x : RealProjectiveThree) = ULift.up (Quotient.mk' y) ↔ _
    rw [ULift.up.injEq]
    exact Quotient.eq
  local_diffeomorph := by
    intro x
    exact (projective_quotient_localDiffeomorph x).comp
      (𝓡 3) (ULift.{u} RealProjectiveThree)
      (projectiveLiftDiffeomorph.symm.isLocalDiffeomorph (Quotient.mk' x))

/-- Compactness uses the literal quotient of the compact unit sphere. -/
theorem projective_compactSpace : CompactSpace RealProjectiveThree := by
  infer_instance

/-- The literal quotient is connected because its unit-sphere source is. -/
theorem projective_connectedSpace : ConnectedSpace RealProjectiveThree := by
  letI : ConnectedSpace UnitThreeSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  infer_instance

/-- The open quotient of the second-countable sphere remains second countable. -/
theorem projective_secondCountable : SecondCountableTopology RealProjectiveThree :=
  isQuotientMap_quotient_mk'.secondCountableTopology projective_open_quotient.isOpenMap

attribute [local instance] projective_t2 projective_compactSpace projective_connectedSpace
  projective_secondCountable

/-- The literal lifted projective carrier keeps the constructed atlas and
quotient topology, with its Borel measurable space. -/
noncomputable def projectiveCarrier : GeneralizedSliceCarrier.{u} := by
  letI : MeasurableSpace (ULift.{u} RealProjectiveThree) :=
    borel (ULift.{u} RealProjectiveThree)
  exact {
    carrier := ULift.{u} RealProjectiveThree
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := ⟨rfl⟩
    chartedSpace := projectiveLiftChartedSpace
    isManifold := projective_lift_isManifold
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := Homeomorph.ulift.secondCountableTopology }

/-- The constructed closed projective summand has the descended sphere
metric, its compatible connection and constant positive sectional curvature. -/
noncomputable def projectiveSpaceform : SurgeryPositiveSpaceform projectiveCarrier.{u} where
  metric := projectiveMetric liftedProjectiveCover
  connection := projectiveConnection liftedProjectiveCover
  compact := by
    letI : CompactSpace (ULift.{u} RealProjectiveThree) :=
      Homeomorph.ulift.symm.surjective.compactSpace Homeomorph.ulift.symm.continuous
    change IsCompact (Set.univ : Set (ULift.{u} RealProjectiveThree))
    exact isCompact_univ
  connected := by
    letI : ConnectedSpace (ULift.{u} RealProjectiveThree) :=
      Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
    change IsConnected (Set.univ : Set (ULift.{u} RealProjectiveThree))
    exact isConnected_univ
  round := projective_constantPositiveSectionalCurvature _ _

end PoincareMT.M38
