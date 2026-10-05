import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Limit.CoordinateRicci
import PoincareLib.Geometry.RicciFlow.Limit.TimeDerivative
import PoincareLib.Geometry.Riemannian.Connection.ChangeMetric

/-!
# Passing the Ricci equation at included time endpoints

Second spatial metric jets and actual first within-time derivatives
preserve the Ricci equation. The limit connection is constructed by
changing the metric of a source reference connection. This is the
equation-preservation step of Morgan--Tian Proposition 5.14, pp. 90-91,
including the terminal time used in Claim 10.11, p. 255;
see task derivation 09.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.RicciFlow

/-- Actual spatial jets and actual within-time derivatives pass the Ricci
equation to a positive smooth metric limit on the full included interval
(Morgan--Tian Proposition 5.14; task derivation 09). -/
theorem equation_of_within_coordinate_jets
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
      Tendsto (fun k => derivWithin (fun s => ((Fseq k).metric s).inner x u v) J t) atTop
        (𝓝 (derivWithin (fun s => (g s).inner x u v) J t))) :
    ∀ t ∈ J, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x u v) (-2 * (D t).ricci x u v) J t := by
  intro t ht x u v
  have hRic := LeviCivitaData.tendsto_ricci_of_coordinate_jets
    (fun k => (Fseq k).connection t) (D t) x u v (hspace t ht x)
  have heq (k : ℕ) : derivWithin (fun s => ((Fseq k).metric s).inner x u v) J t =
      -2 * ((Fseq k).connection t).ricci x u v :=
    ((Fseq k).equation t ht x u v).derivWithin (hJ t ht)
  have hlimit : derivWithin (fun s => (g s).inner x u v) J t = -2 * (D t).ricci x u v := by
    apply tendsto_nhds_unique (htime t ht x u v)
    simpa only [heq] using hRic.const_mul (-2)
  rw [← hlimit]
  exact ((hg.contDiffWithinAt_inner_time ht x u v).differentiableWithinAt
    (by simp)).hasDerivWithinAt

/-- A positive smooth metric limit with the stated genuine coordinate
jets is an actual Ricci flow on the entire source interval, including its
endpoints. The connection is constructed, not an added input
(Morgan--Tian Proposition 5.14; task derivation 09). -/
theorem exists_of_within_coordinate_jets
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n M J)
    (g : ℝ → RiemannianMetric n M)
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
      Tendsto (fun k => derivWithin (fun s => ((Fseq k).metric s).inner x u v) J t) atTop
        (𝓝 (derivWithin (fun s => (g s).inner x u v) J t))) :
    ∃ F : RicciFlow n M J, F.metric = g := by
  let D : ∀ t, LeviCivitaData (g t) := fun t => ((Fseq 0).connection 0).withMetric (g t)
  exact ⟨{
    metric := g
    connection := D
    interval := (Fseq 0).interval
    nontrivial := (Fseq 0).nontrivial
    smooth := hg
    equation := equation_of_within_coordinate_jets Fseq g D hJ hg hspace htime }, rfl⟩

end PoincareMT.RicciFlow
