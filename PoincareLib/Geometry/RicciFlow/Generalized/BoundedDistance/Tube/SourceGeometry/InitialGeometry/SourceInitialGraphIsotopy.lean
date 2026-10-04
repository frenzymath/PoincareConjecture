import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.InitialGeometry.SourceInitialGraphSide
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeVolume
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckGraphIsotopy
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Local.Geometry.LocalPairIsotopy

/-!
# Essentiality of the actual retained initial graph

The literal narrow graph contracts within the same zero node. Compose
with that node's stored tube isotopy, retaining the actual source carrier.
Source: Morgan--Tian Claim 10.8, p. 254; M28 derivation 124.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.SourceTubeData

variable {epsilon C A D0 D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D0 D}
  {S : CounterexampleNeckSegment E}

/-- A retained smooth initial graph is isotopic to the actual cylinder
middle sphere inside the original source tube. Its graph bounds suffice;
no new orientation, coordinate choice or separation is assumed.
Source: Claim 10.8, p. 254; M28 derivation 124. -/
theorem initial_graph_isotopic_middle (T : SourceTubeData S)
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hbound : ∀ q, |f q| < epsilon⁻¹ / 32) :
    SmoothSphereIsotopicIn (T.carrierOpen : Set _)
      (range (fun q => (T.list.node 0).2.coordinate_map (q, f q)))
      T.tube.cylinder.middleSphere := by
  have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
  have hactive : (0 : ℤ) ∈ T.list.active := by
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega
  have heps : (T.list.node 0).2.epsilon = epsilon := T.list.node_epsilon hactive
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr (heps ▸ (T.list.node 0).2.epsilon_pos)
  have hdom (q : UnitTwoSphere) : f q ∈
      Ioo (-(T.list.node 0).2.epsilon⁻¹) (T.list.node 0).2.epsilon⁻¹ := by
    rw [heps]
    have h := abs_lt.mp (hbound q)
    constructor <;> linarith [h.1, h.2]
  have hNT : (T.list.node 0).2.carrier ⊆ (T.carrierOpen : Set _) := by
    intro x hx
    rw [T.carrier_eq_iUnion_nodes]
    exact mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr hlen, hx⟩
  have hmiddle : SmoothSphereIsotopicIn (T.carrierOpen : Set _)
      (T.list.node 0).2.central_sphere T.tube.cylinder.middleSphere := by
    change SmoothSphereIsotopicIn T.tube.carrier
      (T.list.node 0).2.central_sphere T.tube.cylinder.middleSphere
    have h := T.tube.central_sphere_isotopy 0 T.isLeast_tube_chain_zero.1
    simpa only [T.tube_chain_readout.2] using h
  exact ((neck_graph_isotopic_central (T.list.node 0).2 f hf hdom).mono_m28 hNT).trans hmiddle

end PoincareMT.M28.SourceTubeData
