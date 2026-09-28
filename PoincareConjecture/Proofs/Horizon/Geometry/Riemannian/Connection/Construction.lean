import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.CanonicalDomain
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Descent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private def chartDiffeomorph (p : M) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) M (EuclideanSpace ℝ (Fin n)) ∞ :=
  { toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin n)) p).toPartialEquiv
    open_source := (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source
    open_target := (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }

private theorem chartInverse_localDiffeomorph (p : M)
    [Nonempty (chartAt (EuclideanSpace ℝ (Fin n)) p).target] :
    let U := (chartAt (EuclideanSpace ℝ (Fin n)) p).target
    let hU := (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞
      (fun y : U => (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y) := by
  let U := (chartAt (EuclideanSpace ℝ (Fin n)) p).target
  let hU := (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  change IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞
    (fun y : U => (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)
  intro y
  exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n) U hU ∞ y).comp
    (𝓡 n) M ((chartDiffeomorph p).symm.isLocalDiffeomorphAt
      (𝓡 n) (𝓡 n) ∞ y.property)

noncomputable def leviCivitaData (g : RiemannianMetric n M) : LeviCivitaData g := by
  let U (p : M) := (chartAt (EuclideanSpace ℝ (Fin n)) p).target
  let hU (p : M) : IsOpen (U p) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target
  letI (p : M) : Nonempty (U p) :=
    ⟨⟨chartAt (EuclideanSpace ℝ (Fin n)) p p,
      (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source (mem_chart_source _ p)⟩⟩
  letI (p : M) := (hU p).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI (p : M) := (hU p).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 n) (n := ∞)
  let e (p : M) (y : U p) := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y
  have he (p : M) : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e p) :=
    chartInverse_localDiffeomorph p
  exact g.leviCivitaDataOfCover
    (fun p => g.pullbackOfLocalDiffeomorph (e p) (he p))
    (fun p => canonicalMetricLeviCivitaData (U p) (hU p)
      (g.pullbackOfLocalDiffeomorph (e p) (he p))) e
    (fun p => (he p).contMDiff)
    (fun p y => ⟨(he p).mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
    (fun _ _ _ _ => rfl)
    (fun p => ⟨p, ⟨chartAt (EuclideanSpace ℝ (Fin n)) p p,
      (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source (mem_chart_source _ p)⟩,
      (chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv (mem_chart_source _ p)⟩)

end PoincareConjecture.RiemannianMetric
