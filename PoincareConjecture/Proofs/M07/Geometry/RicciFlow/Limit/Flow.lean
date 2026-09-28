import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.Equation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.OpenDomain
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.CoordinateTime
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.ChangeMetric











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter

namespace PoincareConjecture.RicciFlow




theorem exists_of_scalar_coordinate_jets
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n M J)
    (g : ℝ → RiemannianMetric n M)
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
    (htime : ∀ t ∈ J, ∀ (x : M) (a b : Fin n),
      Tendsto (fun k => deriv (fun s => ((Fseq k).metric s).pullbackCoefficients
        (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)
        (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) t) atTop
        (𝓝 (deriv (fun s => (g s).pullbackCoefficients
          (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) t))) :
    ∃ F : RicciFlow n M J, F.metric = g := by
  let D : ∀ t, LeviCivitaData (g t) := fun t => ((Fseq 0).connection 0).withMetric (g t)
  have htime' := fun t ht x =>
    RiemannianMetric.tendsto_inner_time_deriv_of_coordinate_deriv
      (fun k => (Fseq k).metric) g (fun k => (Fseq k).smooth) hg hJ ht x (htime t ht x)
  exact ⟨{
    metric := g
    connection := D
    interval := (Fseq 0).interval
    nontrivial := (Fseq 0).nontrivial
    smooth := hg
    equation := equation_of_coordinate_jets Fseq g D hJ hg hspace htime' }, rfl⟩



theorem exists_of_coordinate_jets_on_open
    {n : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n U J)
    (g : ℝ → RiemannianMetric n U)
    (hJ : IsOpen J) (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hspace : ∀ t ∈ J, ∀ x : U, ∀ r : ℕ, r ≤ 2 → ∀ a c : Fin n,
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => ((Fseq k).metric t).pullbackCoefficients
          (extChartAt (𝓡 n) x).symm y
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ c)) (extChartAt (𝓡 n) x x)) atTop
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => (g t).pullbackCoefficients (extChartAt (𝓡 n) x).symm y
            (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ c)) (extChartAt (𝓡 n) x x))))
    (htime : ∀ t ∈ J, ∀ (x : U) (u v : TangentSpace (𝓡 n) x),
      Tendsto (fun k => deriv (fun s => ((Fseq k).metric s).inner x u v) t) atTop
        (𝓝 (deriv (fun s => (g s).inner x u v) t))) :
    ∃ F : RicciFlow n U J, F.metric = g := by
  let D : ∀ t, LeviCivitaData (g t) := fun t => (g t).openEuclideanLeviCivitaData U
  exact ⟨{
    metric := g
    connection := D
    interval := (Fseq 0).interval
    nontrivial := (Fseq 0).nontrivial
    smooth := hg
    equation := equation_of_coordinate_jets Fseq g D hJ hg hspace htime }, rfl⟩

end PoincareConjecture.RicciFlow
