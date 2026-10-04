import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonComplementComponents
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonAffineImage
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePlanarShear

/-!
# Polygonal Jordan separation without coordinate restrictions

A generic ambient shear removes vertical edges. The crossing
index then separates the complement, and the local-side argument
gives exactly two components with the polygon as common frontier.
See Erickson, Simple Polygons, pp. 2--4 and M76 derivation 99.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)

include hP hinj

/-- The complement of every simple planar polygon is disconnected,
with no restrictions on edge directions. See Erickson pp. 2--4
and M76 derivation 99. -/
theorem not_isPreconnected_compl : ¬ IsPreconnected (P.boundary ℝ)ᶜ := by
  obtain ⟨e, he⟩ := (finite_range P).exists_planar_coordinates_injOn_fst
  let f := e.toLinearEquiv.toAffineEquiv.toAffineMap
  let Q := P.affineImage f
  have hf : Function.Injective f := e.injective
  have hQ : Q.HasSimplicialEdges := P.hasSimplicialEdges_affineImage hP f hf
  have hQi : Function.Injective Q := e.injective.comp hinj
  have hfirst : Function.Injective (fun i => (Q i).1) := by
    intro i j hij
    exact hinj (he (mem_range_self i) (mem_range_self j) hij)
  have hnv : Q.HasNonverticalEdges := by
    intro i hi
    have hrot := (hfirst hi).symm
    have h1 : (1 : Fin (n + 3)) = 0 := add_left_cancel
      (show i + 1 = i + 0 by simpa only [finRotate_apply, add_zero] using hrot)
    have hval := congrArg Fin.val h1
    change 1 % (n + 3) = 0 at hval
    rw [Nat.mod_eq_of_lt (by omega)] at hval
    exact Nat.one_ne_zero hval
  have hboundary : Q.boundary ℝ = e '' P.boundary ℝ := P.affineImage_boundary f
  have hcompl : e '' (P.boundary ℝ)ᶜ = (Q.boundary ℝ)ᶜ := by
    rw [hboundary]
    exact e.toHomeomorph.image_compl _
  intro hconn
  apply Q.not_isPreconnected_compl_of_nonvertical hQ hQi hnv
  rw [← hcompl]
  exact hconn.image e e.continuous.continuousOn

/-- Exactly two distinct connected components exhaust the complement
of a simple planar polygon. See Erickson pp. 2--4 and M76 derivation 99. -/
theorem exists_distinct_two_complement_components :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      connectedComponentIn (P.boundary ℝ)ᶜ a ≠ connectedComponentIn (P.boundary ℝ)ᶜ b ∧
      (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ a ∪
        connectedComponentIn (P.boundary ℝ)ᶜ b := by
  obtain ⟨a, ha, b, hb, hcover⟩ := P.exists_two_complement_components hP hinj
  refine ⟨a, ha, b, hb, ?_, hcover⟩
  intro heq
  have hsingle : (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ b := by
    simpa only [heq, union_self] using hcover
  apply P.not_isPreconnected_compl hP hinj
  rw [hsingle]
  exact isPreconnected_connectedComponentIn

/-- A simple polygon has two nonempty disjoint open connected
complementary regions, with exactly its whole boundary as their
common frontier. See Erickson pp. 2--4 and M76 derivation 99. -/
theorem exists_complementary_regions :
    ∃ U V : Set (ℝ × ℝ), IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ (P.boundary ℝ)ᶜ = U ∪ V ∧
      frontier U = P.boundary ℝ ∧ frontier V = P.boundary ℝ := by
  obtain ⟨a, ha, b, hb, hne, hcover⟩ := P.exists_distinct_two_complement_components hP hinj
  refine ⟨connectedComponentIn (P.boundary ℝ)ᶜ a,
    connectedComponentIn (P.boundary ℝ)ᶜ b,
    P.isClosed_boundary.isOpen_compl.connectedComponentIn,
    P.isClosed_boundary.isOpen_compl.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr ha,
    isConnected_connectedComponentIn_iff.mpr hb, ?_, hcover,
    P.frontier_complement_component hP hinj ha, P.frontier_complement_component hP hinj hb⟩
  exact Set.disjoint_left.mpr fun _ hqa hqb =>
    hne ((connectedComponentIn_eq hqa).trans (connectedComponentIn_eq hqb).symm)

end Polygon
