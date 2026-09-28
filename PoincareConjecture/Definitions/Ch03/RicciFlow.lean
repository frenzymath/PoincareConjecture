import PoincareConjecture.Definitions.Ch01.Curvature
import Mathlib.Analysis.Calculus.Deriv.Basic











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture


def RiemannianMetric.IsSmoothFamilyOn {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : ℝ → RiemannianMetric n M) (J : Set ℝ) : Prop :=
  ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
    ((𝓡 n).prod 𝓘(ℝ,
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
    (fun p : ℝ × M ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      p.2 ((g p.1).inner p.2)) (J ×ˢ Set.univ)


structure RicciFlow (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (J : Set ℝ) where

  metric : ℝ → RiemannianMetric n M

  connection (t : ℝ) : LeviCivitaData (metric t)

  interval : J.OrdConnected

  nontrivial : J.Nontrivial

  smooth : RiemannianMetric.IsSmoothFamilyOn metric J

  equation (t : ℝ) (ht : t ∈ J) (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (metric s).inner x u v)
      (-2 * (connection t).ricci x u v) J t

end PoincareConjecture
