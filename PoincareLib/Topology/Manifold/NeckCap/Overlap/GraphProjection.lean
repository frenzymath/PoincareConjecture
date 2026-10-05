import PoincareLib.Topology.Manifold.NeckCap.Overlap.GraphTransport
import PoincareLib.Topology.Covering.SimplyConnected
import PoincareLib.Topology.Homotopy.Sphere
import PoincareLib.Geometry.Manifold.InverseFunction.LocalDiffeomorph

/-!
# Extracting a height graph from a locally invertible sphere projection

A sphere lying in a neck whose spherical coordinate projection is a local
homeomorphism is a global height graph. Compactness makes the projection a
covering, and simple connectedness of the two-sphere makes that covering
one-sheeted. The inverse projection gives the continuous height function.

This supplies the topological graph step in Morgan--Tian Proposition A.11(4),
pp. 503-504, and Lemma A.20, p. 508. Containment and local invertibility of
the projection are the separate geometric inputs.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- A sphere in the neck with locally invertible spherical projection is
the graph of a continuous height function on the full two-sphere. -/
theorem exists_continuous_graph_of_isLocalHomeomorph
    (f : UnitTwoSphere → M) (hf : Continuous f)
    (hmem : ∀ q, f q ∈ N.carrier)
    (hp : IsLocalHomeomorph (fun q => (N.coordinate_inverse (f q)).1)) :
    ∃ h : UnitTwoSphere → ℝ, Continuous h ∧
      (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
      range f = range (fun q => N.coordinate_map (q, h q)) := by
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  have hcover := isLocalHomeomorph_iff_isCoveringMap.mp hp
  have hbij := Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected hcover
  let e : UnitTwoSphere ≃ₜ UnitTwoSphere := hp.toHomeomorphOfBijective hbij
  let h : UnitTwoSphere → ℝ := fun q => (N.coordinate_inverse (f (e.symm q))).2
  have hh : Continuous h :=
    (N.coordinate_inverse_smooth.continuousOn.comp_continuous
      (hf.comp e.symm.continuous) (fun q => hmem (e.symm q))).snd
  have hgraph (q : UnitTwoSphere) :
      N.coordinate_map (q, h q) = f (e.symm q) := by
    have hz : (q, h q) = N.coordinate_inverse (f (e.symm q)) :=
      Prod.ext (e.apply_symm_apply q).symm rfl
    exact (congrArg N.coordinate_map hz).trans
      (N.coordinate_map_coordinate_inverse (hmem (e.symm q)))
  refine ⟨h, hh, (fun q => (N.coordinate_inverse_mem _ (hmem (e.symm q))).2), ?_⟩
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨e p, ?_⟩
    simpa only [e.symm_apply_apply] using hgraph (e p)
  · rintro ⟨q, rfl⟩
    exact ⟨e.symm q, (hgraph q).symm⟩

/-- A central sphere contained in another neck is a continuous graph when
its spherical coordinate projection is a local homeomorphism. -/
theorem exists_continuous_centralSphere_graph_of_isLocalHomeomorph
    (N' : EpsilonNeck g) (hsubset : N'.central_sphere ⊆ N.carrier)
    (hp : IsLocalHomeomorph
      (fun q : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (q, 0))).1)) :
    ∃ h : UnitTwoSphere → ℝ, Continuous h ∧
      (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
      N'.central_sphere = range (fun q => N.coordinate_map (q, h q)) := by
  obtain ⟨h, hh, hdom, hrange⟩ := N.exists_continuous_graph_of_isLocalHomeomorph
    (fun q => N'.coordinate_map (q, 0)) N'.centralSphere_contMDiff.continuous
    (fun q => hsubset (N'.centralSphere_range ▸ mem_range_self q)) hp
  exact ⟨h, hh, hdom, N'.centralSphere_range.symm.trans hrange⟩

/-- Nonsingularity of the spherical projection derivative makes the projection
a local homeomorphism. Smoothness follows from sphere containment in the neck. -/
theorem centralSphere_projection_isLocalHomeomorph_of_bijective_mfderiv
    (N' : EpsilonNeck g) (hsubset : N'.central_sphere ⊆ N.carrier)
    (hbij : ∀ q, Function.Bijective
      (mfderiv (𝓡 2) (𝓡 2)
        (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, 0))).1) q)) :
    IsLocalHomeomorph
      (fun q : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (q, 0))).1) := by
  apply IsLocalDiffeomorph.isLocalHomeomorph (I := 𝓡 2) (J := 𝓡 2) (n := ∞)
  apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv (hbij := hbij)
  have hc : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : UnitTwoSphere => N.coordinate_inverse (N'.coordinate_map (q, 0))) := by
    intro q
    exact (N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds
        (hsubset (N'.centralSphere_range ▸ mem_range_self q)))).comp q
      (N'.centralSphere_contMDiff q)
  exact contMDiff_fst.comp hc

variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [T3Space M]

/-- Containment and a locally invertible spherical projection imply agreement
of the exact component-relative separation labels. -/
theorem isSeparating_iff_of_centralSphere_projection_isLocalHomeomorph
    (N' : EpsilonNeck g) (hsubset : N'.central_sphere ⊆ N.carrier)
    (hp : IsLocalHomeomorph
      (fun q : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (q, 0))).1)) :
    N.IsSeparating ↔ N'.IsSeparating := by
  obtain ⟨h, hh, hdom, hsphere⟩ :=
    N.exists_continuous_centralSphere_graph_of_isLocalHomeomorph N' hsubset hp
  exact N.isSeparating_iff_of_central_sphere_graph N' h hh hdom hsphere

/-- A central sphere contained in a neck has the same separation label when
its spherical projection has bijective derivative everywhere. -/
theorem isSeparating_iff_of_centralSphere_projection_bijective_mfderiv
    (N' : EpsilonNeck g) (hsubset : N'.central_sphere ⊆ N.carrier)
    (hbij : ∀ q, Function.Bijective
      (mfderiv (𝓡 2) (𝓡 2)
        (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, 0))).1) q)) :
    N.IsSeparating ↔ N'.IsSeparating :=
  N.isSeparating_iff_of_centralSphere_projection_isLocalHomeomorph N' hsubset
    (N.centralSphere_projection_isLocalHomeomorph_of_bijective_mfderiv N' hsubset hbij)

end PoincareMT.EpsilonNeck
