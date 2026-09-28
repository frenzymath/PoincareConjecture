import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.ChartFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.BallTransfer














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space




theorem exists_source_flows_on_retained_chart
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {J : Set ℝ} (F : ∀ k, RicciFlow n (S.carrier k).carrier J)
    (q : G.limitCarrier.carrier)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hUK : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ K)
    (hKchart : K ⊆ (extChartAt (𝓡 n) q).target) :
    ∃ N : ℕ, ∃ Fchart : ℕ → RicciFlow n U J,
      ∀ k (t : ℝ) (x : U) (v w : TangentSpace (𝓡 n) x),
        ((Fchart k).metric t).inner x v w =
          ((F (G.subsequence (max N k))).metric t).pullbackCoefficients
            ((fun y => ((G.embedding (max N k)).toFun (0, y)).2) ∘
              (extChartAt (𝓡 n) q).symm) x v w := by
  classical
  have hcont : ContinuousOn (extChartAt (𝓡 n) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKchart
  obtain ⟨N, hN⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hcont)
  let e (i : ℕ) :=
    (G.embedding i).spatialHomeomorph (G.exhaustion_open i) hzero
  let d (i : ℕ) : PartialDiffeomorph (𝓡 n) (𝓡 n) G.limitCarrier.carrier
      (S.carrier (G.subsequence i)).carrier ∞ := {
    toPartialEquiv := (e i).toPartialEquiv
    open_source := (e i).open_source
    open_target := (e i).open_target
    contMDiffOn_toFun := fun x hx =>
      ((G.embedding i).spatialMap_contMDiffAt (G.exhaustion_open i) hzero hx).contMDiffWithinAt
    contMDiffOn_invFun := by
      rintro _ ⟨x, hx, rfl⟩
      exact ((G.embedding i).spatialInverse_contMDiffAt
        (G.exhaustion_open i) hzero hx).contMDiffWithinAt }
  let c : PartialDiffeomorph (𝓡 n) (𝓡 n) G.limitCarrier.carrier
      (EuclideanSpace ℝ (Fin n)) ∞ := {
    toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin n)) q).toPartialEquiv
    open_source := (chartAt (EuclideanSpace ℝ (Fin n)) q).open_source
    open_target := (chartAt (EuclideanSpace ℝ (Fin n)) q).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hcmap : (c.symm : EuclideanSpace ℝ (Fin n) → G.limitCarrier.carrier) =
      (extChartAt (𝓡 n) q).symm := by
    rw [extChartAt_coe_symm]
    rfl
  have hctarget : c.target = (extChartAt (𝓡 n) q).target := by
    simp only [extChartAt_target, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ]
    rfl
  let Φ (i : ℕ) := c.symm.trans (d i)
  have hΦmap (i : ℕ) :
      (Φ i : EuclideanSpace ℝ (Fin n) → (S.carrier (G.subsequence i)).carrier) =
        (fun y => ((G.embedding i).toFun (0, y)).2) ∘ (extChartAt (𝓡 n) q).symm := by
    change (fun y => ((G.embedding i).toFun (0, y)).2) ∘
      (c.symm : EuclideanSpace ℝ (Fin n) → G.limitCarrier.carrier) = _
    rw [hcmap]
  have hΦsource (i : ℕ) : (Φ i).source =
      (extChartAt (𝓡 n) q).target ∩ (extChartAt (𝓡 n) q).symm ⁻¹' G.exhaustion i := by
    change c.target ∩ (c.symm : EuclideanSpace ℝ (Fin n) → G.limitCarrier.carrier) ⁻¹'
      G.exhaustion i = _
    rw [hctarget, hcmap]
  have hU (k : ℕ) : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ (Φ (max N k)).source := by
    rw [hΦsource]
    intro x hx
    exact ⟨hKchart (hUK hx), G.exhaustion_monotone (le_max_left N k)
      (hN (mem_image_of_mem _ (hUK hx)))⟩
  let Fchart (k : ℕ) :=
    (F (G.subsequence (max N k))).pullbackToPartialChart (Φ (max N k)) U (hU k)
  refine ⟨N, Fchart, ?_⟩
  intro k t x v w
  change (((F (G.subsequence (max N k))).pullbackToPartialChart
    (Φ (max N k)) U (hU k)).metric t).inner x v w = _
  rw [RicciFlow.pullbackToPartialChart_inner, hΦmap]

end PoincareConjecture.M30
