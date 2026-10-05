import PoincareLib.Geometry.RicciFlow.Limit.CoordinateRicci
import PoincareLib.Geometry.RicciFlow.Limit.TimeDerivative

/-!
# Equation retention on closed time domains

Second spatial coordinate jets give convergence of the actual Ricci tensors.
Convergence of first within-time derivatives then passes the source equations
to the limit on a unique-differentiability time domain. In particular the
domain may be `Iic 0`, so its terminal time is retained.

This is the closed-time equation step needed for the annular limits in
Kleiner--Lott (corrected 2013), Theorem 41.2, Case 1, pp. 2674--2675.
The proof follows the equation-retention step of Morgan--Tian,
Proposition 5.14, pp. 90--91, already implemented for open time domains in
`Geometry/RicciFlow/Limit/Equation.lean`. Joint smoothness and convergence
of the within-time derivatives remain explicit inputs here.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RicciFlow

/-- Spatial coordinate jets and first within-time derivatives preserve the
Ricci-flow equation, including boundary times of a unique-differentiability
domain. This theorem does not assert the required spacetime extraction. -/
theorem equation_of_coordinate_jets_within
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n M J)
    (g : ℝ → RiemannianMetric n M) (D : ∀ t, LeviCivitaData (g t))
    (hJ : UniqueDiffOn ℝ J) (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hspace : ∀ t ∈ J, ∀ x : M, ∀ r : ℕ, r ≤ 2 → ∀ a c : Fin n,
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => ((Fseq k).metric t).pullbackCoefficients
          (extChartAt (𝓡 n) x).symm y
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ c)) (extChartAt (𝓡 n) x x)) atTop
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => (g t).pullbackCoefficients (extChartAt (𝓡 n) x).symm y
            (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ c)) (extChartAt (𝓡 n) x x))))
    (htime : ∀ t ∈ J, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      Tendsto (fun k => derivWithin (fun s => ((Fseq k).metric s).inner x u v) J t)
        atTop (𝓝 (derivWithin (fun s => (g s).inner x u v) J t))) :
    ∀ t ∈ J, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x u v) (-2 * (D t).ricci x u v) J t := by
  intro t ht x u v
  have hRic := LeviCivitaData.tendsto_ricci_of_coordinate_jets
    (fun k => (Fseq k).connection t) (D t) x u v (hspace t ht x)
  have heq (k : ℕ) : derivWithin (fun s => ((Fseq k).metric s).inner x u v) J t =
      -2 * ((Fseq k).connection t).ricci x u v :=
    ((Fseq k).equation t ht x u v).derivWithin (hJ t ht)
  have hlimit : derivWithin (fun s => (g s).inner x u v) J t =
      -2 * (D t).ricci x u v := by
    apply tendsto_nhds_unique (htime t ht x u v)
    simpa only [heq] using hRic.const_mul (-2)
  rw [← hlimit]
  exact ((hg.contDiffWithinAt_inner_time ht x u v).differentiableWithinAt
    (by simp)).hasDerivWithinAt

end PoincareMT.RicciFlow
