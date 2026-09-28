import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Connection.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Homothety

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureOnFields_swap (D : LeviCivitaData g)
    (X Y Z : (p : M) → TangentSpace (𝓡 n) p) (x : M) :
    D.curvatureOnFields X Y Z x = -D.curvatureOnFields Y X Z x := by
  unfold LeviCivitaData.curvatureOnFields
  rw [VectorField.mlieBracket_swap_apply (V := X) (W := Y), map_neg]
  abel

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

end PoincareConjecture.Homothety
