import PoincareLib.Geometry.Riemannian.Curvature.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/Ch03/RicciFlow.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/


/-!
# Ordinary Ricci flow on a fixed manifold

Morgan-Tian, Definitions 3.1-3.2, printed p. 35, specifies a smooth evolving
metric on a nondegenerate interval. The total metric and connection families
are representatives; joint smoothness and the equation concern only the time
domain. Included endpoints use within-interval derivatives. No flow or
connection is constructed from an admitted existence theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Joint within-domain smoothness of an evolving metric's bilinear section. -/
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

/-- Ordinary Ricci flow on a nondegenerate real interval and a fixed manifold. -/
structure RicciFlow (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (J : Set ℝ) where
  /-- Total representatives of the smooth spatial metrics on J. -/
  metric : ℝ → RiemannianMetric n M
  /-- Compatible connection data, retained without an existence construction. -/
  connection (t : ℝ) : LeviCivitaData (metric t)
  /-- The time domain is an interval. -/
  interval : J.OrdConnected
  /-- The interval contains at least two distinct times. -/
  nontrivial : J.Nontrivial
  /-- Joint smoothness of the actual metric on the specified spacetime domain. -/
  smooth : RiemannianMetric.IsSmoothFamilyOn metric J
  /-- The metric evolution equation, including one-sided endpoint derivatives. -/
  equation (t : ℝ) (ht : t ∈ J) (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (metric s).inner x u v)
      (-2 * (connection t).ricci x u v) J t

end PoincareMT
