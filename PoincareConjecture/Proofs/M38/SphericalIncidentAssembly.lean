import PoincareConjecture.Proofs.M38.SphericalCollaredComplement
import PoincareConjecture.Proofs.M38.CollaredIncidentComparison
import PoincareConjecture.Proofs.M38.ComponentSpaceforms
import PoincareConjecture.Proofs.M38.SumAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem spherical_incident_component_assembly
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) {U : Set sphereCarrier.{u}.carrier}
    (hU : IsOpen U) (hconnected : IsConnected U)
    (E : SurgeryRegionEquivalence sphereCarrier.{u}
      (componentCarrier (incidentOldCarrier F T hT) x) U univ)
    (f : incidentCapIndex F T hT P x → UnitTwoSphere → sphereCarrier.{u}.carrier)
    (hf : ∀ i, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (range (f i)) (range (f j)))
    (hfrontier : frontier U = ⋃ i, range (f i))
    (c : incidentCapIndex F T hT P x →
      OpenPartialHomeomorph RoundCylinderSpace sphereCarrier.{u}.carrier)
    (hc : ∀ i, ContMDiffOn CylModel (𝓡 3) ∞ (c i) (c i).source)
    (hci : ∀ i, ContMDiffOn (𝓡 3) CylModel ∞ (c i).symm (c i).target)
    (δ : incidentCapIndex F T hT P x → ℝ) (hδ : ∀ i, 0 < δ i)
    (hsource : ∀ i, univ ×ˢ Ioo (-δ i) (δ i) ⊆ (c i).source)
    (hzero : ∀ i z, c i (z, 0) = f i z)
    (hpositive : ∀ i (z : UnitTwoSphere) (s : ℝ), 0 < s → s < δ i →
      c i (z, s) ∈ U)
    (hcompare : ∀ i (z : UnitTwoSphere) (s : ℝ), 0 < s → s < δ i →
      (E.map (c i (z, s))).val.val = (P i.val).collar (z, s)) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3) sphereCarrier.{u}.carrier A.carrier ∞,
      (∀ y ∈ U, d y = incidentOldInclusion F T hT P x (E.map y)) ∧
      Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  classical
  let A := componentCarrier (cappedDiscardedCarrier F T hT P)
    (cappedOldInclusion F T hT P x)
  obtain ⟨B, r, hr, _, hBsep, hUB, hBmatch⟩ :=
    exists_spherical_collared_region_complement hU hconnected f hf hdisjoint hfrontier
      c hc hci δ hδ hsource hzero hpositive
  obtain ⟨d, hd, _⟩ := exists_incident_diffeomorph_of_matched_balls F T hT P x
    sphereCarrier E B hBsep hUB (fun i => c i) r δ (fun i => (hr i).1) hδ hBmatch hcompare
  have hcompact : IsCompact (univ : Set A.carrier) := by
    rw [← image_univ_of_surjective d.surjective]
    apply IsCompact.image _ d.contMDiff.continuous
    change IsCompact (univ : Set (ULift.{u} UnitThreeSphere))
    exact isCompact_univ
  let e : Diffeomorph (𝓡 3) (𝓡 3) sphereCarrier.{u}.carrier UnitThreeSphere ∞ := {
    toEquiv := (Homeomorph.ulift : sphereCarrier.{u}.carrier ≃ₜ UnitThreeSphere).toEquiv
    contMDiff_toFun := threeManifold_down_contMDiff UnitThreeSphere
    contMDiff_invFun := threeManifold_up_contMDiff UnitThreeSphere }
  refine ⟨d, ?_, ⟨spaceformAlongDiffeomorph A threeSphereMetric threeSphereConnection
    (d.symm.trans e) hcompact (componentCarrier_connected _ _)
    (threeSphere_constantPositiveSectionalCurvature threeSphereConnection)⟩,
    ⟨(singletonDisjointUnion A).toAssembly⟩⟩
  intro y hy
  exact hd y hy

end PoincareConjecture.M38
