import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.VertexOrbitCount
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.PermutationOrbitSign









set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.vertices]

local notation "L" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex

noncomputable local instance : DecidableEq K.vertices := Classical.decEq _

open Classical in
theorem even_euler_count_of_all_edge_signs
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hlinks : ∀ v : K.vertices,
      (K.faceLink {v.val}).vertexAbstractComplex.edgeGraph.Preconnected)
    (number : K.vertices ↪ ℕ)
    (sigma : Triangle L → ZMod 2)
    (hcancel : ∀ t u : Triangle L, t ≠ u → ∀ s : Edge L,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1)
    (hcofaces : ∀ e : Edge L, (triangleCofaces L e).card = 2) :
    Even (Fintype.card K.vertices + Fintype.card (Edge L) +
      Fintype.card (Triangle L)) := by
  choose p hp himage hordered using fun t : Triangle L =>
    exists_numbered_triangle_enumeration number t.val t.property.2
  let rho := surfaceTriangleRotation L p hp himage sigma * surfaceEdgePairing L hcofaces
  have hs := Equiv.Perm.sign_eq_pow_card_add_orbits_of_no_fixed_points rho
    (surfaceVertexRotation_ne_self L p hp himage sigma hcofaces)
  change Equiv.Perm.sign
    (surfaceTriangleRotation L p hp himage sigma * surfaceEdgePairing L hcofaces) = _ at hs
  rw [sign_surfaceVertexRotation] at hs
  change (-1 : ℤˣ) ^ Fintype.card (Edge L) =
    (-1 : ℤˣ) ^ (Fintype.card (SurfaceDart L) + Nat.card
      (Quotient (Equiv.Perm.SameCycle.setoid
        (surfaceTriangleRotation L p hp himage sigma * surfaceEdgePairing L hcofaces)))) at hs
  rw [card_surfaceDart L hcofaces,
    K.card_surfaceVertexRotation_orbits hpure (by intro v; convert! hlinks v)
      number p hp himage hordered sigma hcancel hcofaces] at hs
  have hs' : (-1 : ℤ) ^ Fintype.card (Edge L) =
      (-1 : ℤ) ^ (2 * Fintype.card (Edge L) + Fintype.card K.vertices) := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using congrArg Units.val hs
  have hv : Even (Fintype.card K.vertices + Fintype.card (Edge L)) := by
    apply (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)).mp
    rw [pow_add]
    have htwo : (-1 : ℤ) ^ (2 * Fintype.card (Edge L)) = 1 := by
      simp [pow_mul]
    rw [pow_add, htwo, one_mul] at hs'
    rw [← hs', ← pow_two]
    rw [← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  exact hv.add (even_card_triangles_of_two_cofaces L hcofaces)

end Geometry.SimplicialComplex
