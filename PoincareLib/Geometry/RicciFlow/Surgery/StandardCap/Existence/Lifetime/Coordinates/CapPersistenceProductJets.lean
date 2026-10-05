import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Coordinates.CapPersistenceEuclideanJets

/-!
# Returning Euclidean neck estimates to the native product coordinates

The fixed inverse parameter map preserves every coordinate literally.
Linear precomposition therefore transfers finite estimates with the
actual product and Euclidean operator norms. Source: Morgan--Tian
Proposition 9.79(3), p. 234; cap-persistence-implementation.md, section 3.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The inverse of the fixed Euclidean-to-product parameter map. -/
noncomputable def capPersistenceEuclideanCoordinates : RoundCylinderCoordinates →L[ℝ] E₃ :=
  ((EuclideanSpace.proj 0).comp (ContinuousLinearMap.fst ℝ E₂ ℝ)).smulRight
      (EuclideanSpace.single 0 1) +
    ((EuclideanSpace.proj 1).comp (ContinuousLinearMap.fst ℝ E₂ ℝ)).smulRight
      (EuclideanSpace.single 1 1) +
    (ContinuousLinearMap.snd ℝ E₂ ℝ).smulRight (EuclideanSpace.single 2 1)

/-- The inverse parameter map retains the literal three coordinates. -/
theorem capPersistenceEuclideanCoordinates_apply (p : RoundCylinderCoordinates) :
    capPersistenceEuclideanCoordinates p = WithLp.toLp 2 ![p.1 0, p.1 1, p.2] := by
  ext i
  fin_cases i <;> simp [capPersistenceEuclideanCoordinates]

/-- Composing the two actual parameter maps recovers every product vector. -/
theorem capPersistenceProductCoordinates_inverse (p : RoundCylinderCoordinates) :
    capPersistenceProductCoordinates (capPersistenceEuclideanCoordinates p) = p := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [capPersistenceProductCoordinates,
      cylinderHorizontal_apply, capPersistenceEuclideanCoordinates_apply]
  · simp [capPersistenceProductCoordinates, capPersistenceEuclideanCoordinates_apply]

/-- The native product-coordinate derivative is bounded by the literal
Euclidean derivative and the fixed inverse-map operator norm. The target
may be any real normed space (Proposition 9.79(3), p. 234). -/
theorem capPersistence_product_jet_le_euclidean
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : RoundCylinderCoordinates → F) (s : ℝ) (j : ℕ)
    (hf : ContDiffAt ℝ (j : ℕ∞ω)
      (fun x : E₃ => f (capPersistenceProductCoordinates x + (0, s))) 0) :
    ‖iteratedFDeriv ℝ j f (0, s)‖ ≤
      ‖iteratedFDeriv ℝ j (fun x : E₃ =>
        f (capPersistenceProductCoordinates x + (0, s))) 0‖ *
          ‖capPersistenceEuclideanCoordinates‖ ^ j := by
  let F0 := fun x : E₃ => f (capPersistenceProductCoordinates x + (0, s))
  have heq : F0 ∘ capPersistenceEuclideanCoordinates =
      (fun y : RoundCylinderCoordinates => f (y + (0, s))) := by
    funext y
    simp only [Function.comp_apply, F0, capPersistenceProductCoordinates_inverse]
  have h := capPersistenceEuclideanCoordinates.norm_iteratedFDeriv_comp_right_of_contDiffAt
    (x := (0 : RoundCylinderCoordinates)) (by simpa only [map_zero] using hf)
  rw [heq, iteratedFDeriv_comp_add_right, zero_add, map_zero] at h
  exact h

end PoincareMT.M34
