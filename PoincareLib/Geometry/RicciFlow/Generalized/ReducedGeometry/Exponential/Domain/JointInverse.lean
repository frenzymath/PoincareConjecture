import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Domain.JointLocalInverse

/-!
# The inverse on the full joint image

Joint injectivity identifies every local inverse with one selected
inverse. The image is open, and the selected inverse is smooth and
continuous there. Empty joint domains require no selected point.
Morgan-Tian Proposition 6.28, p. 117.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- The selected inverse on the actual joint image, totalized by zero
elsewhere. No point is chosen from an empty joint domain,
Proposition 6.28, p. 117. -/
noncomputable def jointEndpointInverse (E : M14ExponentialFamily G T x)
    (q : G.Point) : G.Horizontal x × ℝ := by
  classical
  exact if h : ∃ z : G.Horizontal x × ℝ, z ∈ M14JointDomain G E ∧ E.gamma z.1 z.2 = q then
    h.choose else 0

/-- On the joint image the selected inverse belongs to the exact
joint domain and recovers the endpoint, Proposition 6.28, p. 117. -/
theorem jointEndpointInverse_spec (E : M14ExponentialFamily G T x) {q : G.Point}
    (hq : q ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) :
    jointEndpointInverse E q ∈ M14JointDomain G E ∧
      E.gamma (jointEndpointInverse E q).1 (jointEndpointInverse E q).2 = q := by
  classical
  have h : ∃ z : G.Horizontal x × ℝ, z ∈ M14JointDomain G E ∧ E.gamma z.1 z.2 = q := by
    obtain ⟨z, rfl⟩ := hq
    exact ⟨z.val, z.property, rfl⟩
  simpa only [jointEndpointInverse, dif_pos h] using h.choose_spec

/-- The selected inverse recovers every joint-domain parameter,
Proposition 6.28, p. 117. -/
theorem jointEndpointInverse_left (E : M14ExponentialFamily G T x)
    (z : M14JointDomain G E) : jointEndpointInverse E (E.gamma z.1.1 z.1.2) = z.val := by
  have h := jointEndpointInverse_spec E (mem_range_self z)
  exact stableGraph_endpoint_injective E h.1.1 z.property.1 h.2

/-- The exact image of the joint-domain endpoint map is open in the
actual spacetime, including its physical boundary, Proposition 6.28,
p. 117. -/
theorem jointMap_range_isOpen (E : M14ExponentialFamily G T x) :
    IsOpen (range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨z, rfl⟩
  obtain ⟨O, hO, hpO, inv, _, hmem, hright⟩ := exists_jointMap_local_inverse E z.property
  exact mem_of_superset (hO.mem_nhds hpO) (fun q hq => ⟨⟨inv q, hmem q hq⟩, hright q hq⟩)

/-- The inverse on the entire joint image is smooth because actual
local inverses agree by joint injectivity, Proposition 6.28, p. 117. -/
theorem jointEndpointInverse_smooth (E : M14ExponentialFamily G T x) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    ContMDiffOn (spacetimeModel n) (𝓘(ℝ, G.Horizontal x × ℝ)) ∞ (jointEndpointInverse E)
      (range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  change ContMDiffOn (spacetimeModel n) (𝓘(ℝ, G.Horizontal x × ℝ)) ∞ (jointEndpointInverse E) _
  rintro q ⟨z, rfl⟩
  obtain ⟨O, hO, hpO, inv, hsm, hmem, hright⟩ := exists_jointMap_local_inverse E z.property
  have hagree : jointEndpointInverse E =ᶠ[𝓝 (E.gamma z.1.1 z.1.2)] inv := by
    filter_upwards [hO.mem_nhds hpO] with q hq
    have hi := jointEndpointInverse_spec E
      (show q ∈ range (fun w : M14JointDomain G E => E.gamma w.1.1 w.1.2) from
        ⟨⟨inv q, hmem q hq⟩, hright q hq⟩)
    exact stableGraph_endpoint_injective E hi.1.1 (hmem q hq).1 (hi.2.trans (hright q hq).symm)
  exact ((hsm.contMDiffAt (hO.mem_nhds hpO)).congr_of_eventuallyEq hagree).contMDiffWithinAt

/-- The selected joint inverse is continuous on its actual image,
Proposition 6.28, p. 117. -/
theorem jointEndpointInverse_continuous (E : M14ExponentialFamily G T x) :
    ContinuousOn (jointEndpointInverse E)
      (range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  exact (jointEndpointInverse_smooth E).continuousOn

/-- Every open subset of the joint domain has open endpoint image,
Proposition 6.28, p. 117. -/
theorem jointMap_isOpenMap (E : M14ExponentialFamily G T x) :
    IsOpenMap (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) := by
  intro S hS
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hS
  have heq : (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) ''
      (Subtype.val ⁻¹' U) =
      range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) ∩ jointEndpointInverse E ⁻¹' U := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨mem_range_self z, by simpa only [mem_preimage, jointEndpointInverse_left E z] using hz⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      exact ⟨z, by simpa only [mem_preimage, jointEndpointInverse_left E z] using hz, rfl⟩
  rw [heq]
  exact (jointEndpointInverse_continuous E).isOpen_inter_preimage (jointMap_range_isOpen E) hU

end PoincareMT.M14
