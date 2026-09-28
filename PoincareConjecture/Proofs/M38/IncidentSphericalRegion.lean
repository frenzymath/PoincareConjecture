import PoincareConjecture.Proofs.M38.SphericalIncidentAssembly
import PoincareConjecture.Proofs.M38.ComponentBoundaryIncidence
import PoincareConjecture.Proofs.M38.CompactRegionImages
import PoincareConjecture.Proofs.M38.PartialHomeomorphRegions
import PoincareConjecture.Proofs.M38.UnionRefinement
import PoincareConjecture.Proofs.M38.CompactCollarInjectivity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.Slice










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]



noncomputable def incidentOldAmbientEquivalence (x : eventDiscardedOpen F T hT) :
    SurgeryRegionEquivalence (componentCarrier (incidentOldCarrier F T hT) x)
      (F.slice (F.event T hT).tMinus) univ
      (connectedComponentIn (F.event T hT).retained_preᶜ x.val) := by
  let J := composeRegions (componentRegionEquivalence (incidentOldCarrier F T hT) x)
    (restrictRegions
      (openRegionEquivalence (F.slice (F.event T hT).tMinus) (eventDiscardedOpen F T hT) x)
      (connectedComponent x) (subset_univ _))
  have htarget :
      (openRegionEquivalence (F.slice (F.event T hT).tMinus)
        (eventDiscardedOpen F T hT) x).map '' connectedComponent x =
      connectedComponentIn (F.event T hT).retained_preᶜ x.val :=
    (connectedComponentIn_eq_image
      (show x.val ∈ (F.event T hT).retained_preᶜ from x.property)).symm
  exact {
    map := J.map
    inverse := J.inverse
    map_image := J.map_image.trans htarget
    inverse_image := by simpa only [← htarget] using J.inverse_image
    left_inverse := J.left_inverse
    right_inverse := by simpa only [← htarget] using J.right_inverse
    map_smooth := J.map_smooth
    inverse_smooth := by simpa only [← htarget] using J.inverse_smooth }


theorem incidentOldAmbientEquivalence_map (x : eventDiscardedOpen F T hT)
    (y : (componentCarrier (incidentOldCarrier F T hT) x).carrier) :
    (incidentOldAmbientEquivalence F T hT x).map y = y.val.val := rfl

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)




structure IncidentComponentRegion (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (Q : GeneralizedSliceCarrier.{u}) where
  region : Set Q.carrier
  open_region : IsOpen region
  connected : IsConnected region
  identify : SurgeryRegionEquivalence Q (componentCarrier (incidentOldCarrier F T hT) x)
    region univ
  sphere : incidentCapIndex F T hT P x → UnitTwoSphere → Q.carrier
  sphere_smooth : ∀ i, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (sphere i)
  sphere_disjoint : ∀ i j, i ≠ j → Disjoint (range (sphere i)) (range (sphere j))
  frontier_eq : frontier region = ⋃ i, range (sphere i)
  collar : incidentCapIndex F T hT P x → OpenPartialHomeomorph RoundCylinderSpace Q.carrier
  collar_smooth : ∀ i, ContMDiffOn CylModel (𝓡 3) ∞ (collar i) (collar i).source
  collar_inverse_smooth : ∀ i, ContMDiffOn (𝓡 3) CylModel ∞ (collar i).symm (collar i).target
  width : incidentCapIndex F T hT P x → ℝ
  width_pos : ∀ i, 0 < width i
  collar_source : ∀ i, univ ×ˢ Ioo (-width i) (width i) ⊆ (collar i).source
  collar_zero : ∀ i z, collar i (z, 0) = sphere i z
  collar_positive : ∀ i (z : UnitTwoSphere) (s : ℝ), 0 < s → s < width i →
    collar i (z, s) ∈ region
  collar_negative : ∀ i (z : UnitTwoSphere) (s : ℝ), -width i < s → s < 0 →
    collar i (z, s) ∉ closure region
  collar_compare : ∀ i (z : UnitTwoSphere) (s : ℝ), 0 < s → s < width i →
    (identify.map (collar i (z, s))).val.val = (P i.val).collar (z, s)



theorem exists_incident_component_region
    (P : ∀ i, EventCapCoordinates F T hT i) (x : eventDiscardedOpen F T hT)
    (Q : GeneralizedSliceCarrier.{u})
    (e : OpenPartialHomeomorph (F.slice (F.event T hT).tMinus).carrier
      Q.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆
      e.source) :
    ∃ R : IncidentComponentRegion F T hT P x Q,
      R.region = e '' connectedComponentIn (F.event T hT).retained_preᶜ x.val := by
  classical
  let Ω := connectedComponentIn (F.event T hT).retained_preᶜ x.val
  have hΩsource : Ω ⊆ e.source := subset_closure.trans hsource
  let U := e '' Ω
  have hΩopen : IsOpen Ω := by
    let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
      ChartedSpace.locallyConnectedSpace StandardCapSpace _
    exact (F.event T hT).retained_pre_compact.isClosed.isOpen_compl.connectedComponentIn
  have hU : IsOpen U := e.isOpen_image_of_subset_source hΩopen hΩsource
  have hconnected : IsConnected U :=
    (isConnected_connectedComponentIn_iff.mpr x.property).image _
      (e.continuousOn.mono hΩsource)
  let E₀ := incidentOldAmbientEquivalence F T hT x
  let J := restrictRegions (partialHomeomorphRegions e he hi) Ω hΩsource
  let E := reverseRegions (composeRegions E₀ J)
  let c : incidentCapIndex F T hT P x →
      OpenPartialHomeomorph RoundCylinderSpace Q.carrier :=
    fun i => (P i.val).collarChart.trans e
  have hc (i) : ContMDiffOn CylModel (𝓡 3) ∞ (c i) (c i).source :=
    he.comp ((event_cap_collar_smooth F T hT i.val (P i.val).width_pos
      (P i.val).width_lt (P i.val).shell_domain).mono inter_subset_left) inter_subset_right
  have hci (i) : ContMDiffOn (𝓡 3) CylModel ∞ (c i).symm (c i).target :=
    (event_cap_collar_inverse_smooth F T hT i.val (P i.val).width_pos
      (P i.val).width_lt (P i.val).shell_domain).comp
        (hi.mono inter_subset_left) inter_subset_right
  have hzeroSource (i : incidentCapIndex F T hT P x) (z : UnitTwoSphere) :
      (z, (0 : ℝ)) ∈ (c i).source := by
    refine ⟨by simp [EventCapCoordinates.collarChart], ?_⟩
    exact hsource (((P i.val).central_mem_component_closure_iff x z).mpr i.property)
  choose d hd hstrip using fun i =>
    exists_uniform_product_ball (c i).open_source (0 : ℝ) (hzeroSource i)
  let δ := fun i => min (d i) 1
  have hδ (i) : 0 < δ i := lt_min (hd i) zero_lt_one
  have hδ1 (i) : δ i ≤ 1 := min_le_right _ _
  have hcsource (i) : univ ×ˢ Ioo (-δ i) (δ i) ⊆ (c i).source := by
    intro z hz
    apply hstrip i
    refine ⟨mem_univ _, ?_⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_lt.mpr hz.2).trans_le (min_le_left _ _)
  let f : incidentCapIndex F T hT P x → UnitTwoSphere → Q.carrier :=
    fun i z => c i (z, 0)
  have hf (i) : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i) :=
    (c i).isSmoothEmbedding_slice (hc i) (hci i)
      (ContinuousLinearEquiv.ofFinrankEq (by simp)) 0 (hzeroSource i)
  have hpositiveOld (i : incidentCapIndex F T hT P x) (z : UnitTwoSphere) (s : ℝ)
      (hs : 0 < s) (hsδ : s < δ i) : (P i.val).collar (z, s) ∈ Ω :=
    (P i.val).positive_collar_subset_component x i.property
      ⟨(z, s), ⟨mem_univ _, hs, hsδ.trans_le (hδ1 i)⟩, rfl⟩
  have hpositive (i) (z : UnitTwoSphere) (s : ℝ) (hs : 0 < s) (hsδ : s < δ i) :
      c i (z, s) ∈ U := ⟨(P i.val).collar (z, s), hpositiveOld i z s hs hsδ, rfl⟩
  have hnegative (i : incidentCapIndex F T hT P x) (z : UnitTwoSphere) (s : ℝ)
      (hsδ : -δ i < s) (hs : s < 0) : c i (z, s) ∉ closure U := by
    intro hy
    rw [← partialHomeomorph_image_closure e
      (event_discarded_component_closure_compact F T hT x.val) hsource] at hy
    obtain ⟨w, hw, hew⟩ := hy
    have hcs := hcsource i (show (z, s) ∈ univ ×ˢ Ioo (-δ i) (δ i) from
      ⟨mem_univ _, hsδ, hs.trans (hδ i)⟩)
    have hwc : w = (P i.val).collar (z, s) := e.injOn (hsource hw) hcs.2 hew
    have hcl : (P i.val).collar (z, s) ∈ closure (F.event T hT).retained_preᶜ :=
      hwc ▸ closure_mono (connectedComponentIn_subset _ _) hw
    rw [closure_compl] at hcl
    exact hcl ((P i.val).negative_interior
      ⟨(z, s), ⟨mem_univ _, by linarith [hδ1 i], hs⟩, rfl⟩)
  have hcompare (i) (z : UnitTwoSphere) (s : ℝ) (hs : 0 < s) (hsδ : s < δ i) :
      (E.map (c i (z, s))).val.val = (P i.val).collar (z, s) := by
    have hp := hpositiveOld i z s hs hsδ
    change (E₀.inverse (e.symm (e ((P i.val).collar (z, s))))).val.val = _
    rw [e.left_inv (hΩsource hp)]
    exact E₀.right_inverse hp
  have hfrontier : frontier U = ⋃ i, range (f i) := by
    rw [← partialHomeomorph_image_frontier e
      (event_discarded_component_closure_compact F T hT x.val) hsource]
    rw [event_component_frontier F T hT P x, image_iUnion]
    apply iUnion_congr
    intro i
    rw [← (P i.val).collar_central, ← image_comp]
    ext y
    constructor
    · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
      have hs0 : s = 0 := hs
      subst s
      exact mem_range_self z
    · rintro ⟨z, rfl⟩
      exact ⟨(z, 0), by simp, rfl⟩
  have hdisjoint (i j : incidentCapIndex F T hT P x) (hij : i ≠ j) :
      Disjoint (range (f i)) (range (f j)) := by
    apply disjoint_left.mpr
    rintro y ⟨z, hz⟩ ⟨w, hw⟩
    have hcenter : (P i.val).collar (z, 0) = (P j.val).collar (w, 0) :=
      e.injOn (hzeroSource i z).2 (hzeroSource j w).2 (hz.trans hw.symm)
    exact disjoint_left.mp ((P i.val).collars_disjoint (P j.val)
      (fun h => hij (Subtype.ext h)))
        ⟨(z, 0), by simp, rfl⟩ ⟨(w, 0), by simp, hcenter.symm⟩
  exact ⟨{
    region := U
    open_region := hU
    connected := hconnected
    identify := E
    sphere := f
    sphere_smooth := hf
    sphere_disjoint := hdisjoint
    frontier_eq := hfrontier
    collar := c
    collar_smooth := hc
    collar_inverse_smooth := hci
    width := δ
    width_pos := hδ
    collar_source := hcsource
    collar_zero := fun _ _ => rfl
    collar_positive := hpositive
    collar_negative := hnegative
    collar_compare := hcompare }, rfl⟩





theorem spherical_incident_assembly_of_component_chart
    (P : ∀ i, EventCapCoordinates F T hT i) (x : eventDiscardedOpen F T hT)
    (e : OpenPartialHomeomorph (F.slice (F.event T hT).tMinus).carrier
      sphereCarrier.{u}.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆
      e.source) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  obtain ⟨R, _⟩ := exists_incident_component_region F T hT P x sphereCarrier e he hi hsource
  obtain ⟨_, _, hspaceform, hassembly⟩ := spherical_incident_component_assembly F T hT P x
    R.open_region R.connected R.identify R.sphere R.sphere_smooth R.sphere_disjoint
    R.frontier_eq R.collar R.collar_smooth R.collar_inverse_smooth R.width R.width_pos
    R.collar_source R.collar_zero R.collar_positive R.collar_compare
  exact ⟨hspaceform, hassembly⟩

end PoincareConjecture.M38
