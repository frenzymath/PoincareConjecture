import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.CoordinateRicci
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.TimeDerivative









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter

namespace PoincareConjecture.RicciFlow



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

end PoincareConjecture.RicciFlow
