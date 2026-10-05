import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Homology.Local
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Euclidean.PositiveLinearHomotopy

/-!
# Positive linear maps on local homology

M02 constructs a puncture-preserving homotopy from the identity to every
positive linear automorphism of Euclidean three-space. Relative homotopy
invariance makes its action on local homology the identity. This is the
positive part of Hatcher, Section 2.2, Exercise 7, p. 155, and Section 3.3,
p. 233, used for Morgan--Tian Theorem 0.3 footnote 2, p. xii.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set

namespace Poincare.Topology.Orientation.ProjectivePlane

open Poincare.Topology

/-- A positive linear automorphism induces the identity on the homology of
the punctured Euclidean pair. Source: Hatcher, Section 2.2, Exercise 7,
p. 155; Section 3.3, p. 233. -/
theorem positiveLinear_relativeHomologyMap
    (L : EuclideanSpace Real (Fin 3) ≃L[Real] EuclideanSpace Real (Fin 3))
    (hL : 0 < L.toLinearEquiv.toLinearMap.det) (d : Nat) :
    homologyMap (integralRelativeMap (⟨L, L.continuous⟩ :
      C(EuclideanSpace Real (Fin 3), EuclideanSpace Real (Fin 3)))
      (A := ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))))
      (B := ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))))
      (by intro x hx h; exact hx (L.injective (h.trans L.map_zero.symm)))) d =
        𝟙 (LocalHomology (EuclideanSpace Real (Fin 3)) 0 d) := by
  obtain ⟨H, hH⟩ := exists_positive_linear_puncture_homotopy L hL
  have h := relativeHomologyMap_eq_of_homotopy H
    (A := ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))))
    (B := ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))))
    (fun _ hx => hx)
    (by intro x hx h; exact hx (L.injective (h.trans L.map_zero.symm))) hH d
  rw [← h]
  exact localHomologyMap_id 0 d

end Poincare.Topology.Orientation.ProjectivePlane
