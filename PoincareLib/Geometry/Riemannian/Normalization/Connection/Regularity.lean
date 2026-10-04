import PoincareLib.Geometry.Riemannian.Normalization.Connection.KoszulFunctional
import PoincareLib.Geometry.Riemannian.Normalization.Connection.Smoothness
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Local regularity of the explicit Levi-Civita connection

The coordinate proof uses the local Koszul identity and smooth inversion of a
positive Gram matrix, as in Morgan-Tian, Theorem 1.2 and formula (1.1), printed
pp. 3-4. Applying the resulting operator to a smooth field preserves smoothness.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Smoothness of the connection on a locally smooth section. -/
theorem normalization_contMDiffOn_connection (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (Y : (x : M) → TangentSpace (𝓡 n) x)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun x ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        x (D.connection Y x)) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hA : ∀ (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M},
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x →
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x →
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x →
      g.inner x (D.connection Y x (X x)) (Z x) =
        (1 / 2 : ℝ) * ConnectionExistence.koszulRHS g X Y Z x := by
    intro X Y Z x hX hY hZ
    have hk := D.normalization_koszul X Y Z hX hY hZ
    unfold ConnectionExistence.koszulRHS
    linarith
  exact ConnectionExistence.koszul_operator_contMDiffOn g
    (fun Y x ↦ D.connection Y x) hA hU Y hY

/-- Apply the local regularity obligation to a smooth direction field. -/
theorem normalization_contMDiffOn_connection_apply (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (fun x ↦ D.connection Y x (X x))) U := by
  exact (D.normalization_contMDiffOn_connection hU Y hY).clm_bundle_apply hX

end PoincareMT.LeviCivitaData
