import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Curvature.CapPersistenceScalarModel
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Coordinates.CapPersistenceEuclideanJets

/-!
# A universal neck accuracy for actual scalar curvature

The ordinary order-two error tends to zero with the frozen neck
accuracy. An actual metric realization of the same coefficient germ
therefore has scalar curvature close to one, with the accuracy chosen
before every center, height, tensor and realization.
Source: Morgan--Tian Proposition 9.79(3), p. 234, and Theorem 12.28,
pp. 323-324; cap-persistence-implementation.md, section 3.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The neck accuracy precedes all geometric data. The comparison
metric must have the literal frozen coefficient germ at the origin. -/
theorem capPersistence_exists_scalar_accuracy {eta : ℝ} (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (delta : ℝ), 0 < delta → delta < delta0 →
      ∀ (B : RoundCylinderTwoTensor), RoundCylinderClose delta 0 B →
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-delta⁻¹) delta⁻¹ →
      ∀ (g : RiemannianMetric 3 E₃) (D : LeviCivitaData g),
      (∀ a b : Fin 3, (fun x => g.euclideanCoefficients x
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
        =ᶠ[𝓝 (0 : E₃)] (fun x => roundCylinderTensorCoefficient B (chartAt E₂ q)
          (capPersistenceProductCoordinates x + (0, s)) a b)) →
        |D.scalarCurvature 0 - 1| < eta := by
  obtain ⟨zeta, hzeta, hscalar⟩ := capPersistence_exists_scalar_one_tolerance heta
  obtain ⟨C, hC, hjet⟩ := capPersistence_exists_euclidean_error_jet_bound 2
  let delta0 := min (1 / 4 : ℝ) (zeta / (8 * (C + 1)))
  have hdelta0 : 0 < delta0 := lt_min (by norm_num) (div_pos hzeta (by positivity))
  refine ⟨delta0, hdelta0, ?_⟩
  intro delta hdelta hsmall B hB q s hs g D hgerm
  have hquarter : delta < 1 / 4 := hsmall.trans_le (min_le_left _ _)
  have hz : delta < zeta / (8 * (C + 1)) := hsmall.trans_le (min_le_right _ _)
  have horder : 2 ≤ Nat.floor delta⁻¹ := by
    apply (Nat.le_floor_iff (inv_pos.mpr hdelta).le).mpr
    rw [inv_eq_one_div, le_div_iff₀ hdelta]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hsqrt : Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + 2)) = 4 * delta := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    norm_num only [show (1 / 2 : ℝ) ^ (2 + 2) = 1 / 16 by norm_num]
    ring
  have herr : C * Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + 2)) ≤ zeta := by
    rw [hsqrt]
    have hmul := (lt_div_iff₀ (by positivity : 0 < 8 * (C + 1))).mp hz
    nlinarith
  apply hscalar g D
  intro j hj a b
  have he := (hgerm a b).sub (Filter.EventuallyEq.refl _ _ :
    (fun x : E₃ => stereographicCylinderCoefficients 2 x
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
      =ᶠ[𝓝 (0 : E₃)] _)
  have hd : iteratedFDeriv ℝ j (fun x => g.euclideanCoefficients x
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) -
        stereographicCylinderCoefficients 2 x
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) 0 =
      iteratedFDeriv ℝ j (fun x => roundCylinderTensorCoefficient B (chartAt E₂ q)
        (capPersistenceProductCoordinates x + (0, s)) a b -
          stereographicCylinderCoefficients 2 x
            (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) 0 :=
    (he.iteratedFDeriv ℝ j).self_of_nhds
  rw [hd]
  exact (hjet delta B hB horder q s hs j hj a b).trans herr

end PoincareMT.M34
