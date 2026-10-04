import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.OriginalClosedCircleMap

/-!
# The literal target translation of the original closed handle

The original ambient-to-handle homeomorphism transports the given map.
The fixed three-circle coordinates then define translation in only the
last circle, with its actual quotient-representative formula retained.
See Waldhausen1968, p.60, section1.3, and rigidity056, section3.
-/

set_option autoImplicit false

namespace PoincareMT.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

/-- Transport the actual original map through the fixed ambient-to-handle
comparison. No new source topology or map is chosen. See rigidity056,
section3. -/
noncomputable def hamiltonZeroAmbientMap (phi : C(H0, H0)) : C(X0, X0) :=
  ⟨fun x => hamiltonZeroAmbientEquiv.symm (phi (hamiltonZeroAmbientEquiv x)),
    hamiltonZeroAmbientEquiv.symm.continuous.comp
      (phi.continuous.comp hamiltonZeroAmbientEquiv.continuous)⟩

/-- The transported map retains the same original last circle value.
See rigidity056, sections1 and3. -/
theorem hamiltonZeroAmbientMap_circle (phi : C(H0, H0)) (x : X0) :
    ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
      (hamiltonZeroAmbientMap phi x)).2 = hamiltonZeroCircleMap phi x := by
  change (hamiltonZeroHierarchyCoordinates (hamiltonZeroAmbientEquiv
    (hamiltonZeroAmbientEquiv.symm (phi (hamiltonZeroAmbientEquiv x))))).2 =
      (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).2
  rw [hamiltonZeroAmbientEquiv.apply_symm_apply]

/-- Translate by a real amount in the literal last target circle.
The first two target coordinates remain unchanged. See rigidity056,
section3. -/
noncomputable def hamiltonZeroTargetTranslation : C(ℝ × X0, X0) :=
  let Q := hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
  ⟨fun z => Q.symm ((Q z.2).1, (Q z.2).2 + (z.1 : C0)),
    Q.symm.continuous.comp
      ((Q.continuous.comp continuous_snd).fst.prodMk
        ((Q.continuous.comp continuous_snd).snd.add
          ((AddCircle.continuous_mk' (4 * (16 : ℝ))).comp continuous_fst)))⟩

/-- The complete original coordinate formula for the constructed target
translation holds at every real amount and every ambient point.
See rigidity056, section3. -/
theorem hamiltonZeroTargetTranslation_coordinates (u : ℝ) (y : X0) :
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
      (hamiltonZeroTargetTranslation (u, y)) =
        (((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates) y).1,
          ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates) y).2 +
            (u : C0)) :=
  (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).apply_symm_apply _

/-- Zero translation fixes every original target point. See rigidity056,
section3. -/
theorem hamiltonZeroTargetTranslation_zero (y : X0) :
    hamiltonZeroTargetTranslation (0, y) = y := by
  apply (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).injective
  simpa only [AddCircle.coe_zero, add_zero] using
    hamiltonZeroTargetTranslation_coordinates 0 y

/-- On every original quotient representative the actual translation
adds the displacement to the last real coordinate alone. This is the
literal affine formula used by the later spatial PL argument.
See rigidity056, sections3 and5. -/
theorem hamiltonZeroTargetTranslation_mk (u : ℝ) (x : Fin 0 → ℝ)
    (v : Fin 3 → ℝ) :
    hamiltonZeroTargetTranslation (u, (x, QuotientAddGroup.mk v)) =
      (x, QuotientAddGroup.mk ![v 0, v 1, v 2 + u]) := by
  apply (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).injective
  rw [hamiltonZeroTargetTranslation_coordinates]
  change (((v 0 : C0), (v 1 : C0)), (v 2 : C0) + (u : C0)) =
    (((v 0 : C0), (v 1 : C0)), ((v 2 + u : ℝ) : C0))
  rw [AddCircle.coe_add]

end PoincareMT.M76
