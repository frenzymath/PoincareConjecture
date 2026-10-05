import PoincareLib.Geometry.RicciFlow.Limit.CoordinateRicci
import PoincareLib.Geometry.RicciFlow.Limit.TimeDerivative

/-!
# Passing the Ricci-flow equation to a smooth positive metric limit

Second spatial scalar jets give Ricci convergence. Actual first time
derivatives then pass the source equation to the limit. This is the equation
preservation step of Morgan--Tian, Proposition 5.14, pp. 90--91.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter

namespace PoincareMT.RicciFlow

/-- Smooth positive metric limits preserve the retained Ricci-flow equation.
Only second spatial scalar jets and the actual first time derivatives are used. -/
theorem equation_of_coordinate_jets
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n M J)
    (g : ℝ → RiemannianMetric n M) (D : ∀ t, LeviCivitaData (g t))
    (hJ : IsOpen J) (hg : RiemannianMetric.IsSmoothFamilyOn g J)
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
      Tendsto (fun k => deriv (fun s => ((Fseq k).metric s).inner x u v) t) atTop
        (𝓝 (deriv (fun s => (g s).inner x u v) t))) :
    ∀ t ∈ J, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x u v) (-2 * (D t).ricci x u v) J t := by
  intro t ht x u v
  have hRic := LeviCivitaData.tendsto_ricci_of_coordinate_jets
    (fun k => (Fseq k).connection t) (D t) x u v (hspace t ht x)
  have heq (k : ℕ) : deriv (fun s => ((Fseq k).metric s).inner x u v) t =
      -2 * ((Fseq k).connection t).ricci x u v :=
    (((Fseq k).equation t ht x u v).hasDerivAt (hJ.mem_nhds ht)).deriv
  have hlimit : deriv (fun s => (g s).inner x u v) t = -2 * (D t).ricci x u v := by
    apply tendsto_nhds_unique (htime t ht x u v)
    simpa only [heq] using hRic.const_mul (-2)
  rw [← hlimit]
  exact (hg.hasDerivAt_inner hJ ht x u v).hasDerivWithinAt

end PoincareMT.RicciFlow
