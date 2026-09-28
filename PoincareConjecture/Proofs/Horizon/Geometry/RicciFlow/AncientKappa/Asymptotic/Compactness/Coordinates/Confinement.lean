import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Relative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Surjectivity
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Operations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

def relativeCoordinateDomain
    {n : ℕ} {a b c d : ℝ} {S : PointedFlowSequence n a b} {T : PointedFlowSequence n c d}
    (G : PointedGeometricConvergence S) (L : PointedGeometricConvergence T)
    (f : G.limitCarrier.carrier → L.limitCarrier.carrier)
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (extChartAt (𝓡 n) qG).target ∩
    (fun y ↦ f ((extChartAt (𝓡 n) qG).symm y)) ⁻¹' (extChartAt (𝓡 n) qL).source

theorem isOpen_relativeCoordinateDomain
    {n : ℕ} {a b c d : ℝ} {S : PointedFlowSequence n a b} {T : PointedFlowSequence n c d}
    (G : PointedGeometricConvergence S) (L : PointedGeometricConvergence T)
    (f : G.limitCarrier.carrier → L.limitCarrier.carrier) (hf : Continuous f)
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier) :
    IsOpen (G.relativeCoordinateDomain L f qG qL) := by
  exact (hf.comp_continuousOn
    (contMDiffOn_extChartAt_symm (n := ∞) qG).continuousOn).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓡 n) qG) (isOpen_extChartAt_source (I := 𝓡 n) qL)

theorem exists_compact_relativeCoordinate_target
    {n : ℕ} {C : FlowCarrier.{0} n} {a b c d : ℝ}
    {F : ℕ → BasedFlow n a b C} {H : ℕ → BasedFlow n c d C}
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    {σ : ℕ → ℕ}
    (f : G.limitCarrier.carrier → L.limitCarrier.carrier) (hf : Continuous f)
    (hconv : letI := (L.limitFlow.metricAt 0).toMetricSpace
      ∀ Q : Set G.limitCarrier.carrier, IsCompact Q →
        TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) f atTop Q)
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKΩ : K ⊆ G.relativeCoordinateDomain L f qG qL) :
    ∃ T : Set (EuclideanSpace ℝ (Fin n)), IsCompact T ∧
      T ⊆ (extChartAt (𝓡 n) qL).target ∧
      ∀ᶠ k in atTop,
        MapsTo (G.relativeCoordinateMap L qG qL (σ k)) K (interior T) ∧
        ∀ y ∈ K, ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, (extChartAt (𝓡 n) qG).symm y)).2)).2 ∈
            (extChartAt (𝓡 n) qL).source := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let : LocallyCompactSpace L.limitCarrier.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) _
  let cg := extChartAt (𝓡 n) qG
  let cl := extChartAt (𝓡 n) qL
  have hQc : IsCompact (cg.symm '' K) := hK.image_of_continuousOn
    ((contMDiffOn_extChartAt_symm (n := ∞) qG).continuousOn.mono (fun y hy ↦ (hKΩ hy).1))
  have hQmap : MapsTo f (cg.symm '' K) cl.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hKΩ hy).2
  obtain ⟨R, hR, hRc, hmaps⟩ := exists_compact_target_of_tendstoUniformlyOn hQc
    (isOpen_extChartAt_source (I := 𝓡 n) qL) hf.continuousOn hQmap
    (hconv _ hQc)
  have hcl : ContinuousOn cl R := by
    apply (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := qL)).continuousOn.mono
    simpa only [extChartAt_source] using hRc
  obtain ⟨T, hT, hRT, hTc⟩ := exists_compact_between (hR.image_of_continuousOn hcl)
    (isOpen_extChartAt_target (I := 𝓡 n) qL)
    (by rintro _ ⟨x, hx, rfl⟩; exact cl.map_source (hRc hx))
  refine ⟨T, hT, hTc, ?_⟩
  filter_upwards [hmaps] with k hk
  refine ⟨?_, ?_⟩
  · intro y hy
    exact hRT (mem_image_of_mem cl (hk (mem_image_of_mem cg.symm hy)))
  · intro y hy
    exact hRc (hk (mem_image_of_mem cg.symm hy))

end PoincareConjecture.PointedGeometricConvergence
