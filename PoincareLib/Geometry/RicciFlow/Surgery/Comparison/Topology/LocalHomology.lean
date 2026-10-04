import PoincareLib.AlgebraicTopology.SingularHomology.Homology.IntegralCoverHomology
/-!
# Local relative integral homology

The relative pair obtained from an open neighborhood of a point is canonically
equivalent to the ambient punctured pair. This is the local excision bridge
used to transport a punctured Euclidean class into a manifold chart.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def integralLocalRelativeMap (x : X) (U : Set X) :
    integralRelativeChains
        ((Subtype.val : U → X) ⁻¹' ({x}ᶜ : Set X)) ⟶
      integralRelativeChains ({x}ᶜ : Set X) :=
  integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
    (A := (Subtype.val : U → X) ⁻¹' ({x}ᶜ : Set X))
    (B := ({x}ᶜ : Set X)) (by
      intro y hy
      exact hy)

theorem integral_local_relative_excision
    [T1Space X] (x : X) (U : Set X) (hU : IsOpen U) (hx : x ∈ U) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap
      (integralLocalRelativeMap x U) n) := by
  apply integral_open_cover_excision ({x}ᶜ : Set X) U
    isOpen_compl_singleton hU ?_ n
  apply Set.eq_univ_iff_forall.mpr
  intro y
  by_cases hy : y = x
  · right
    rw [hy]
    exact hx
  · left
    exact hy

end Poincare.Topology
