import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonPLDomainMaps
import Mathlib.Topology.Homotopy.Basic

/-!
# Relative boundary-proper PL approximation input

The input is the actual identity between two structures on one
compact marked domain. The output fixes its boundary throughout
the homotopy and has exactly that boundary as its boundary preimage.
No approximation theorem is proved here. See Hamilton 1976, p. 67
and M76 derivation 320.
-/

set_option autoImplicit false

universe u v w

open Set

namespace PoincareMT.M76

variable {X : Type u} [TopologicalSpace X]
  {ι : Type v} {κ : Type w}

/-- The approximation input needed before Hamilton Lemma 3. The
boundary-properness equation is retained in addition to the relative
homotopy; ordinary properness would not express it. See Hamilton
p. 67 and M76 derivation 320. -/
def HasRelativeBoundaryProperPLApproximation [T2Space X]
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (d : κ → OpenPartialHomeomorph X (Fin 3 → ℝ)) (R : Set X) : Prop :=
  IsCompact R → PLDomain e R → PLDomain d R →
    ∀ U : Set R, IsOpen U → (Subtype.val : R → X) ⁻¹' frontier R ⊆ U →
      ChartwisePLOn e d (ContinuousMap.id R) U →
        ∃ phi : C(R, R), ChartwisePLMap e d phi ∧
          phi ⁻¹' ((Subtype.val : R → X) ⁻¹' frontier R) =
            (Subtype.val : R → X) ⁻¹' frontier R ∧
          Nonempty ((ContinuousMap.id R).HomotopyRel phi
            ((Subtype.val : R → X) ⁻¹' frontier R))

end PoincareMT.M76
