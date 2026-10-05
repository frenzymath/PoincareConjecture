import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalPhaseTargetProducts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.StandardHierarchyParameterPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLComposition

/-!
# Whole finite period-box parameters of the literal target products

The two full tangent periods retain their actual quotient identifications.
The normal coordinate is the affine real translate theta+t. The actual
finite interval products and checked standard quotient parameter certify
the complete box in the original target atlas; no box embedding is claimed.
See Waldhausen1968, p.60, and rigidity056, section6.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E" => ((ℝ × ℝ) × ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

/-- The actual real period-box parameter retains both tangential
quotient identifications and the literal shifted normal coordinate.
See rigidity056, section6. -/
def hamiltonZeroPhaseParameter (theta : ℝ) (z : E) : X0 :=
  (0, QuotientAddGroup.mk ![z.1.1, z.1.2, theta + z.2])

/-- Every real representative gives exactly the same target-product
point in the original ambient space. See rigidity056, section6. -/
theorem hamiltonZeroPhaseParameter_eq_product (theta s t u : ℝ) :
    hamiltonZeroPhaseParameter theta ((s, t), u) =
      hamiltonZeroPhaseProduct theta (((s : C0), (t : C0)), u) := by
  apply (Q0).injective
  rw [hamiltonZeroPhaseProduct_coordinates]
  rfl

/-- The actual standard atlas and interval bounds construct a finite
whole period-box PL certificate, including all period edges and both
closed normal ends. The real box is not asserted injective.
See rigidity056, section6, and its target-fibers consumption note. -/
theorem StandardLatticeHandleAtlas.exists_finite_phase_parameter
    {κ : Type*} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {theta rho : ℝ} (hrho : 0 < rho)
    (hlower : 0 < theta - rho) (hupper : theta + rho < 4 * 16) :
    ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧
      K.space = ((Icc (0 : ℝ) (4 * 16) ×ˢ Icc (0 : ℝ) (4 * 16)) ×ˢ Icc (-rho) rho) ∧
      PolyhedralPLInCharts d (hamiltonZeroPhaseParameter theta) K.space := by
  have hI := isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 4 * 16)
  have hR := isFinitePLBallPair_Icc (show -rho < rho by linarith)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := (hI.prod hI).prod hR
  let a : E →ᴬ[ℝ] E :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ E theta +
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap)
  have ha : FinitePiecewiseAffineOn a K.space :=
    (K.affineOnFaces_affine a).finitePiecewiseAffineOn hK
  have hmap : MapsTo a K.space
      ((Icc (0 : ℝ) (4 * 16) ×ˢ Icc (0 : ℝ) (4 * 16)) ×ˢ Icc (0 : ℝ) (4 * 16)) := by
    intro z hz
    have hz' := hKs.subset hz
    change (z.1, theta + z.2) ∈ _
    exact ⟨hz'.1, by linarith [hz'.2.1], by linarith [hz'.2.2]⟩
  have hPL := hd.polyhedralPL_zeroCutParameter.comp_finitePiecewiseAffineOn K hK ha hmap
  change PolyhedralPLInCharts d (hamiltonZeroPhaseParameter theta) K.space at hPL
  exact ⟨K, hK, hKs, hPL⟩

end PoincareMT.M76
