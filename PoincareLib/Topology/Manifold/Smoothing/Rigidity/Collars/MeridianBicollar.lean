import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.StandardMeridian
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLowerPeriodLattice
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.AddCircleShortArcCharts

/-!
# The original period512 meridian's whole two-sided neighborhood

The actual quotient coordinate gives a product neighborhood of the
whole standard meridian, including its complete boundary fibers.
Its closed coordinate box has full PL certificates in every supplied
standard target atlas. This module concerns the fixed lower-period
consumer, separately from the arbitrary-lattice disk construction.
See Hamilton 1976, p. 65, Waldhausen 1968, pp. 59--60,77--78, and
M76 inputs/Rigidity/derivations/002_standard_meridian.md.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

private instance : Fact (0 < p) := ⟨by norm_num⟩

/-- The exact one-coordinate period512 quotient is the original
additive circle, with no translation of its origin.
See rigidity derivation 002, two-sided neighborhood. -/
noncomputable def hamiltonSolidTorusCircleEquiv : T ≃ₜ AddCircle p :=
  (hamiltonLowerLatticePiEquiv (Fin 1)).trans
    (Homeomorph.funUnique (Fin 1) (AddCircle p))

/-- The one-circle identification retains each literal quotient
representative. See rigidity derivation 002. -/
theorem hamiltonSolidTorusCircleEquiv_mk (t : ℝ) :
    hamiltonSolidTorusCircleEquiv (QuotientAddGroup.mk (fun _ : Fin 1 => t)) =
      (t : AddCircle p) := rfl

/-- Inverse circle coordinates recover the original lattice class.
See rigidity derivation 002. -/
theorem hamiltonSolidTorusCircleEquiv_symm_coe (t : ℝ) :
    hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p) =
      QuotientAddGroup.mk (fun _ : Fin 1 => t) := by
  apply hamiltonSolidTorusCircleEquiv.injective
  rw [hamiltonSolidTorusCircleEquiv.apply_symm_apply,
    hamiltonSolidTorusCircleEquiv_mk]

/-- The two-sided short quotient neighborhood is a concrete open
partial homeomorphism on the entire disk product, including its rim.
See Waldhausen pp. 59--60 and rigidity derivation 002. -/
noncomputable def hamiltonMeridianBicollar : OpenPartialHomeomorph (D × ℝ) H :=
  (OpenPartialHomeomorph.refl D).prod
    ((AddCircle.shortArcQuotient p 1).trans
      hamiltonSolidTorusCircleEquiv.symm.toOpenPartialHomeomorph)

/-- The bicollar has the complete prescribed product source.
See rigidity derivation 002. -/
theorem hamiltonMeridianBicollar_source :
    hamiltonMeridianBicollar.source = univ ×ˢ Ioo (-1) 1 := by
  change univ ×ˢ ((AddCircle.shortArcQuotient p 1).trans
    hamiltonSolidTorusCircleEquiv.symm.toOpenPartialHomeomorph).source = _
  rw [OpenPartialHomeomorph.trans_source]
  change univ ×ˢ ((AddCircle.shortArcQuotient p 1).source ∩
    (AddCircle.shortArcQuotient p 1) ⁻¹' univ) = _
  rw [preimage_univ, inter_univ,
    AddCircle.shortArcQuotient_source p (by norm_num)]

/-- The image is the actual whole short-arc neighborhood in the
original handle. Its relative openness is part of the concrete
open partial homeomorphism. See rigidity derivation 002. -/
theorem hamiltonMeridianBicollar_target :
    hamiltonMeridianBicollar.target =
      {z : H | hamiltonSolidTorusCircleEquiv z.2 ∈
        ((↑) : ℝ → AddCircle p) '' Ioo (-1) 1} := by
  ext z
  change (True ∧ (True ∧ hamiltonSolidTorusCircleEquiv z.2 ∈
    (AddCircle.shortArcQuotient p 1).target)) ↔ _
  rw [AddCircle.shortArcQuotient_target p (by norm_num)]
  simp

/-- Every bicollar value is the original quotient of its signed
transverse parameter. See rigidity derivation 002. -/
theorem hamiltonMeridianBicollar_apply (x : D) (t : ℝ) :
    hamiltonMeridianBicollar (x, t) =
      (x, QuotientAddGroup.mk (fun _ : Fin 1 => t)) := by
  change (x, hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p)) = _
  rw [hamiltonSolidTorusCircleEquiv_symm_coe]

/-- The complete central disk is the original meridian, with its
parametrization retained pointwise. See rigidity derivation 002. -/
theorem hamiltonMeridianBicollar_zero (x : D) :
    hamiltonMeridianBicollar (x, 0) = hamiltonStandardMeridian L x := by
  rw [hamiltonMeridianBicollar_apply]
  rfl

/-- Every lateral fiber meets the original manifold boundary
exactly when its disk parameter is on the whole original rim.
See rigidity derivation 002. -/
theorem hamiltonMeridianBicollar_mem_boundary (x : D) (t : ℝ) :
    hamiltonMeridianBicollar (x, t) ∈ latticeHandleBoundary (Fin 2) (Fin 1) L ↔
      ‖(x : V2)‖ = 1 := by
  rw [hamiltonMeridianBicollar_apply]
  change (‖(x : V2)‖ = 1 ∧ True) ↔ ‖(x : V2)‖ = 1
  exact ⟨And.left, fun hx => ⟨hx, trivial⟩⟩

/-- Forgetting the disk subtype gives exactly the original
lattice projection on the whole signed product coordinate.
See rigidity derivation 002. -/
theorem hamiltonMeridianBicollar_ambient_apply (x : D) (t : ℝ) :
    (((hamiltonMeridianBicollar (x, t)).1 : V2),
      (hamiltonMeridianBicollar (x, t)).2) =
        latticeCoordinateProjection (Fin 2) (Fin 1) L
          (Sum.elim (x : V2) (fun _ : Fin 1 => t)) := by
  rw [hamiltonMeridianBicollar_apply]
  rfl

/-- The full closed bicollar coordinate box is PL in the original
supplied standard atlas. This includes all central and lateral
boundary points. See rigidity derivation 002. -/
theorem StandardLatticeHandleAtlas.polyhedralPL_meridianBox
    {β : Type*}
    {d : β → OpenPartialHomeomorph
      (LatticeHandleAmbient (Fin 2) (Fin 1) L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d) :
    PolyhedralPLInCharts d (latticeCoordinateProjection (Fin 2) (Fin 1) L)
      (closedBall (0 : (Fin 2 ⊕ Fin 1) → ℝ) 1) := by
  obtain ⟨_, C, _, _, _, e, he, _⟩ :=
    (Set.isFinitePLBallPair_unit_cube (ι := Fin 2 ⊕ Fin 1))
  obtain ⟨f, ⟨K, hK, hKD, _⟩, _⟩ := he
  have hi : FinitePiecewiseAffineOn (id : ((Fin 2 ⊕ Fin 1) → ℝ) → _)
      (closedBall (0 : (Fin 2 ⊕ Fin 1) → ℝ) 1) :=
    ⟨K, hK, hKD, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ _)⟩
  exact hd.polyhedralPL_projection hi

end PoincareMT.M76
