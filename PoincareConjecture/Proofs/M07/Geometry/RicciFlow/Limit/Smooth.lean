import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.Flow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.SpacetimeJets












set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Filter Set

namespace PoincareConjecture.RicciFlow



theorem exists_of_smooth_limit
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n M J)
    (g : ℝ → RiemannianMetric n M)
    (hJ : IsOpen J) (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hjets : ∀ (x : M) (r : ℕ) (a b : Fin n)
      (K : Set (ℝ × EuclideanSpace ℝ (Fin n))), IsCompact K →
      K ⊆ J ×ˢ (extChartAt (𝓡 n) x).target →
      TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ r
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2
              (EuclideanSpace.basisFun (Fin n) ℝ a)
              (EuclideanSpace.basisFun (Fin n) ℝ b)) z)
        (fun z => iteratedFDeriv ℝ r
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            (g p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2
              (EuclideanSpace.basisFun (Fin n) ℝ a)
              (EuclideanSpace.basisFun (Fin n) ℝ b)) z) atTop K) :
    ∃ F : RicciFlow n M J, F.metric = g := by
  have hj (t : ℝ) (ht : t ∈ J) (x : M) :=
    RiemannianMetric.spatial_and_time_jets_of_spacetime_jets
      (fun k => (Fseq k).metric) g (fun k => (Fseq k).smooth) hg hJ ht x
      (fun r _ a b => RiemannianMetric.tendsto_spacetime_jet_of_compact_uniform r
        (hjets x r a b) ⟨ht, mem_extChartAt_target x⟩)
  exact exists_of_scalar_coordinate_jets Fseq g hJ hg
    (fun t ht x => (hj t ht x).1) (fun t ht x => (hj t ht x).2)

end PoincareConjecture.RicciFlow
