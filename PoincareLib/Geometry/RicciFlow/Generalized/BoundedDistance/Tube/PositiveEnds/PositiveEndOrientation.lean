import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Geometry.SeparatingNeckComponents

/-!
# Orienting the selected neck toward the retained positive component

Morgan--Tian Claim 10.8, p. 254. The two distinct ambient components show
that the opposite collar misses the retained side. Literal axial reversal
then orients the same neck for the recut in derivation 94.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

/-- Orient the selected neck toward the already retained component.
Its opposite collar is disjoint from that component, by actual ambient
separation (MT Claim 10.8, p. 254; derivation 94). -/
theorem exists_orientation_into_component (N : EpsilonNeck g) (hsep : N.IsSeparating)
    {P : Set M} (hcomponent : ∀ x ∈ P, connectedComponentIn N.central_sphereᶜ x = P)
    (hcollar : N.belowGraph_m28 (fun _ => 0) ⊆ P ∨ N.aboveGraph_m28 (fun _ => 0) ⊆ P) :
    ∃ L : EpsilonNeck g, L.SameUpToReversal N ∧
      L.aboveGraph_m28 (fun _ => 0) ⊆ P ∧ Disjoint (L.belowGraph_m28 (fun _ => 0)) P := by
  have hzero : ∀ q : UnitTwoSphere, (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    fun _ => ⟨neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  obtain ⟨a, ha⟩ := (N.isConnected_belowGraph_m28 _ continuous_const hzero).nonempty
  obtain ⟨b, hb⟩ := (N.isConnected_aboveGraph_m28 _ continuous_const hzero).nonempty
  obtain ⟨_ho0, _ho1, _hc0, _hc1, hd, _hu, _hf0, _hf1, _hcl0, _hcl1,
      hbelow, habove⟩ := N.complement_components_of_isSeparating hsep ha hb
  rcases hcollar with hneg | hpos
  · have hdis : Disjoint (N.aboveGraph_m28 (fun _ => 0)) P := by
      rw [← hcomponent a (hneg ha)]
      exact hd.symm.mono_left habove
    have haR : N.reversed.aboveGraph_m28 (fun _ => 0) = N.belowGraph_m28 (fun _ => 0) := by
      ext x
      simp only [aboveGraph_m28, belowGraph_m28, mem_ofPred_eq, reversed_carrier,
        reversed_coordinate_inverse, neg_pos]
    have hbR : N.reversed.belowGraph_m28 (fun _ => 0) = N.aboveGraph_m28 (fun _ => 0) := by
      ext x
      simp only [aboveGraph_m28, belowGraph_m28, mem_ofPred_eq, reversed_carrier,
        reversed_coordinate_inverse, neg_lt_zero]
    exact ⟨N.reversed, N.reversed_sameUpToReversal, haR.symm ▸ hneg, hbR.symm ▸ hdis⟩
  · refine ⟨N, SameUpToReversal.refl N, hpos, ?_⟩
    rw [← hcomponent b (hpos hb)]
    exact hd.mono_left hbelow

end PoincareMT.EpsilonNeck
