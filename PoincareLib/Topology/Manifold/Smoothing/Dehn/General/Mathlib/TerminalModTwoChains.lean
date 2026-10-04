import PoincareLib.Topology.Manifold.Smoothing.Dehn.Topology.Mathlib.ModTwoCocycleOfClosed
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.TerminalCocycleExactness
import Mathlib.Algebra.Field.ZMod

/-!
# Degree-one chain exactness of the same compact terminal model

Every closed original edge cochain constructs an actual cocycle and
cover. The original terminal obstruction supplies its vertex potential.
Vector-space annihilator identities then give the exact equality of
triangle boundaries and edge cycles on that same finite model.
See Hatcher, Algebraic Topology, pp. 105, 189 and 196--197, and M76 Dehn
derivations 005 and 007. No manifold duality is used here.
-/

set_option autoImplicit false

universe u v

open Set

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  {ι : Type v} [Fintype ι] (A : PreAbstractSimplicialComplex ι)
  (hvertex : ∀ i : ι, {i} ∈ A.faces)
  {N D : Set X} (hDN : D ⊆ N)
  {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
  (hr : ∀ x, r x ∈ D)
  {s : C(N, N)}
  (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
  (hs : ∀ n, (s n : X) ∈ D) (B : A.barycentricSpace ≃ₜ N)
  (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
    [T2Space Y] [ConnectedSpace Y] (p : Y → X),
    IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False)

include hvertex hDN H hr K hs B hterminal

/-- The original edge and triangle incidence maps are cochain exact
on the actual compact terminal model, by the constructed double cover
and the original common deformations. See Dehn derivations 005 and 007. -/
theorem ker_edgeCoboundary_eq_range_vertexCoboundary :
    LinearMap.ker (edgeCoboundary A) = LinearMap.range (vertexCoboundary A) := by
  apply le_antisymm
  · intro z hz
    have hz' : edgeCoboundary A z = 0 := hz
    let c := cocycleOfClosed A z hz'
    have hc : c.IsCoboundary := c.isCoboundary_of_terminal_common_deformation
      hvertex hDN H hr K hs B hterminal
    exact mem_range_vertexCoboundary_of_coboundary A z hz' hc
  · rintro _ ⟨a, rfl⟩
    exact edgeCoboundary_vertexCoboundary A a

/-- Actual triangle boundaries are exactly the actual edge cycles.
The dual spaces have the original simplex evaluation bases, whose
literal incidence formulas were proved in the preceding module.
See Hatcher pp. 189 and 196--197 and Dehn derivation 007. -/
theorem range_boundary2_eq_ker_boundary1 :
    LinearMap.range (edgeCoboundary A).dualMap =
      LinearMap.ker (vertexCoboundary A).dualMap := by
  have hcochain := ker_edgeCoboundary_eq_range_vertexCoboundary A
    hvertex hDN H hr K hs B hterminal
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker (edgeCoboundary A), hcochain,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range (vertexCoboundary A)]

/-- Every original degree-one chain cycle is the boundary of an actual
chain of the original triangles. See Dehn derivation 007. -/
theorem exists_triangle_chain_of_cycle
    (z : Module.Dual (ZMod 2) (Edge A → ZMod 2))
    (hz : (vertexCoboundary A).dualMap z = 0) :
    ∃ t : Module.Dual (ZMod 2) (Triangle A → ZMod 2),
      (edgeCoboundary A).dualMap t = z := by
  have hmem : z ∈ LinearMap.ker (vertexCoboundary A).dualMap := hz
  rw [← range_boundary2_eq_ker_boundary1 A hvertex hDN H hr K hs B hterminal] at hmem
  exact hmem

end PreAbstractSimplicialComplex.ModTwoCochains
