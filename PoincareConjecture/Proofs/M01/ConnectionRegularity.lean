import PoincareConjecture.Proofs.M01.ConnectionExistenceKoszul
import PoincareConjecture.Proofs.M01.ConnectionExistenceRegularity
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem m01_contMDiffOn_connection (D : LeviCivitaData g)
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
    have hk := D.m01_koszul X Y Z hX hY hZ
    unfold ConnectionExistence.koszulRHS
    linarith
  exact ConnectionExistence.koszul_operator_contMDiffOn g
    (fun Y x ↦ D.connection Y x) hA hU Y hY

theorem m01_contMDiffOn_connection_apply (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (fun x ↦ D.connection Y x (X x))) U := by
  exact (D.m01_contMDiffOn_connection hU Y hY).clm_bundle_apply hX

end PoincareConjecture.LeviCivitaData
