import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic
import PoincareLib.AlgebraicTopology.SingularHomology.Homology.IntegralHomologyUniverse
import PoincareLib.AlgebraicTopology.SingularHomology.Sphere.IntegralSphereBase
import PoincareLib.Topology.Manifold.EmbeddedSphere.Parity.Equiv
import Mathlib.Algebra.Group.Int.Even

/-!
# The sphere generator and its local restrictions

The fundamental class of the actual embedded sphere range is not divisible
by two, and neither is its image in local surface homology at any point.
The punctured sphere is contractible, so the canonical relative projection
is an isomorphism. Sources: Hatcher, Corollary 2.14, p. 114, the homology
sequence, pp. 117-118, and local orientations, pp. 233-235. This is an input
to the separation repair for Morgan--Tian, Proposition 15.12 and Remark
15.13, p. 365; see M53 derivation 04.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open Poincare.Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  (S : SmoothEmbeddedNullHomotopicSphere (M := M))

/-- The integral degree-two homology of the sphere range is infinite cyclic,
with universe transport included. Hatcher, Corollary 2.14, p. 114. -/
def sphereRangeHomologyEquiv : integralHomology (Set.range S.sphere) 2 ≃ₗ[Int] Int :=
  (integralHomeomorphHomologyEquiv S.smooth_embedding.isEmbedding.toHomeomorph.symm 2).trans
    (integralSphereH2Iso.toLinearEquiv.trans ULift.moduleEquiv)

/-- A fixed generator of the sphere range, with its sign determined by the
lower sphere homology equivalence. Hatcher, pp. 114 and 233-235. -/
def sphereFundamentalClass : integralHomology (Set.range S.sphere) 2 :=
  (sphereRangeHomologyEquiv S).symm 1

/-- The chosen integral sphere generator is not divisible by two.
Source: Hatcher, Corollary 2.14, p. 114, and M53 derivation 04. -/
theorem sphereFundamentalClass_not_even : ¬ Even (sphereFundamentalClass S) := by
  intro h
  apply Int.not_even_one
  have he : (sphereRangeHomologyEquiv S).toAddEquiv (sphereFundamentalClass S) = 1 :=
    (sphereRangeHomologyEquiv S).apply_symm_apply 1
  rw [← he]
  exact ((sphereRangeHomologyEquiv S).toAddEquiv.even_apply_iff _).mpr h

/-- Deleting any point from the embedded sphere range leaves a contractible
space, via the stereographic chart. Source: M02 `SphereOpenCover` and
Hatcher's homotopy-invariance argument, pp. 110-111; M53 derivation 04. -/
theorem sphereRange_puncture_contractible (x : Set.range S.sphere) :
    ContractibleSpace ({x}ᶜ : Set (Set.range S.sphere)) := by
  let e := S.smooth_embedding.isEmbedding.toHomeomorph.symm
  let ep : ({x}ᶜ : Set (Set.range S.sphere)) ≃ₜ ({e x}ᶜ : Set UnitTwoSphere) :=
    e.subtype (fun y => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, e.injective.eq_iff])
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  obtain ⟨p, _⟩ := exists_sphere_puncture_homeomorph 2 (e x)
  exact (ep.trans p).contractibleSpace

/-- The canonical restriction from global sphere homology to local surface
homology is an isomorphism. Hatcher, homology sequence, pp. 117-118, and
local orientations, pp. 233-235. -/
theorem sphereRange_toLocalHomology_isIso (x : Set.range S.sphere) :
    IsIso (integralToRelativeHomology ({x}ᶜ : Set (Set.range S.sphere)) 2) := by
  let := sphereRange_puncture_contractible S x
  exact integralToRelativeHomology_isIso_of_contractible _ 1

/-- The fixed sphere generator has odd local surface class at every point.
This uses the actual restriction map, not a chosen local isomorphism.
Source: Hatcher, pp. 233-235, and M53 derivation 04. -/
theorem sphereFundamentalClass_local_not_even (x : Set.range S.sphere) :
    ¬ Even (integralToRelativeHomology ({x}ᶜ : Set (Set.range S.sphere)) 2
      (sphereFundamentalClass S)) := by
  let := sphereRange_toLocalHomology_isIso S x
  let e := (asIso (integralToRelativeHomology ({x}ᶜ : Set (Set.range S.sphere)) 2)).toLinearEquiv
  intro h
  exact sphereFundamentalClass_not_even S (e.toAddEquiv.even_apply_iff _ |>.mp h)

end PoincareMT.Topology.EmbeddedSphere
