import PoincareLib.Geometry.Riemannian.Homothety.Connection.Regularity
import PoincareLib.Geometry.Riemannian.Curvature.Basic

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M13/CurvatureTensorial.lean`,
revision `0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See `references/ricci-flow/mapher/rescaling-import.json`. -/

/-!
# Tensoriality in the curvature directions

The first two field arguments are tensorial as soon as the derivative of the
last field is differentiable. All operations use the frozen commutator.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.Homothety

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Antisymmetry in the directional fields uses only the bracket's antisymmetry. -/
theorem curvatureOnFields_swap (D : LeviCivitaData g)
    (X Y Z : (p : M) → TangentSpace (𝓡 n) p) (x : M) :
    D.curvatureOnFields X Y Z x = -D.curvatureOnFields Y X Z x := by
  unfold LeviCivitaData.curvatureOnFields
  rw [VectorField.mlieBracket_swap_apply (V := X) (W := Y), map_neg]
  abel

/-- Tensoriality in the first directional field. -/
theorem curvatureOnFields_tensorial_first (D : LeviCivitaData g)
    (Y Z : (p : M) → TangentSpace (𝓡 n) p) (x : M)
    (hDZ : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (fun p ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q)
        p (D.connection Z p)) x) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun X ↦ D.curvatureOnFields X Y Z x) x where
  smul {f X} hf hX := by
    have hDX := hDZ.clm_bundle_apply hX
    have hfun : (fun p ↦ D.connection Z p ((f • X) p)) =
        f • (fun p ↦ D.connection Z p (X p)) := by
      funext p
      exact map_smul (D.connection Z p) (f p) (X p)
    unfold LeviCivitaData.curvatureOnFields
    rw [hfun, D.connection.isCovariantDerivativeOn.leibniz hDX hf,
      VectorField.mlieBracket_smul_left hf hX]
    rw [show (f • X) x = f x • X x from rfl, map_smul]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul]
    module
  add {X X'} hX hX' := by
    have hDX := hDZ.clm_bundle_apply hX
    have hDX' := hDZ.clm_bundle_apply hX'
    have hfun : (fun p ↦ D.connection Z p ((X + X') p)) =
        (fun p ↦ D.connection Z p (X p)) + (fun p ↦ D.connection Z p (X' p)) := by
      funext p
      exact map_add (D.connection Z p) (X p) (X' p)
    unfold LeviCivitaData.curvatureOnFields
    rw [hfun, D.connection.isCovariantDerivativeOn.add hDX hDX',
      VectorField.mlieBracket_add_left hX hX']
    simp only [Pi.add_apply, add_apply, map_add]
    abel

/-- Tensoriality in the second directional field follows by antisymmetry. -/
theorem curvatureOnFields_tensorial_second (D : LeviCivitaData g)
    (X Z : (p : M) → TangentSpace (𝓡 n) p) (x : M)
    (hDZ : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (fun p ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q)
        p (D.connection Z p)) x) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun Y ↦ D.curvatureOnFields X Y Z x) x where
  smul hf hY := by
    rw [curvatureOnFields_swap, (curvatureOnFields_tensorial_first D X Z x hDZ).smul hf hY,
      curvatureOnFields_swap D X _ Z x, smul_neg]
  add hY hY' := by
    rw [curvatureOnFields_swap,
      (curvatureOnFields_tensorial_first D X Z x hDZ).add hY hY',
      curvatureOnFields_swap D X _ Z x, curvatureOnFields_swap D X _ Z x, neg_add]

end PoincareMT.Homothety
