import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison

set_option autoImplicit false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.SmoothSpacetimeEmbedding

variable {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
  {F : BasedFlow n T' T C} {G : BasedFlow n T' T D}
  {U : Set C.carrier}

theorem spatial_velocity_eq_zero
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U)) (t : ℝ) (x : C.carrier) :
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun s ↦ (e.toFun (s, x)).2) t 1 = 0 := by
  simpa only [F.spacetimeVectorField_spatial_zero, G.spacetimeVectorField_spatial_zero,
    map_zero, add_zero] using e.vector_field_compatible t x

theorem spatial_eq_of_mem
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    {s t : ℝ} (hs : s ∈ Ioo T' T) (ht : t ∈ Ioo T' T)
    {x : C.carrier} (hx : x ∈ U) :
    (e.toFun (s, x)).2 = (e.toFun (t, x)).2 := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let σ : ℝ → D.carrier := fun τ ↦ (e.toFun (τ, x)).2
  have hσ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ σ (Ioo T' T) := by
    intro τ hτ
    exact ((e.smooth_on.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun u hu ↦ ⟨hu, hx⟩)) τ hτ).snd
  have hforward : ∀ a ∈ Ioo T' T, ∀ b ∈ Ioo T' T, a ≤ b → σ a = σ b := by
    intro a ha b hb hab
    have hI : Icc a b ⊆ Ioo T' T := fun τ hτ ↦
      ⟨ha.1.trans_le hτ.1, hτ.2.trans_lt hb.2⟩
    have hlength : (G.flow.metric 0).pathELength σ a b = 0 := by
      rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm]
      simp only [σ, e.spatial_velocity_eq_zero, RiemannianMetric.tangentNorm,
        map_zero, Real.sqrt_zero, ENNReal.ofReal_zero, lintegral_zero]
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : D.carrier → Type _) :=
      ⟨(G.flow.metric 0).toRiemannianMetric⟩
    have hdist : (G.flow.metric 0).edist (σ a) (σ b) ≤ 0 := by
      exact (Manifold.riemannianEDist_le_pathELength ((hσ.mono hI).of_le (by simp))
        rfl rfl hab).trans hlength.le
    let : EMetricSpace D.carrier := D.metricEMetricSpace (G.metricAt 0)
    exact edist_eq_zero.mp (le_antisymm hdist bot_le)
  rcases le_total s t with hst | hts
  · exact hforward s hs t ht hst
  · exact (hforward t ht s hs hts).symm

end PoincareConjecture.SmoothSpacetimeEmbedding

namespace PoincareConjecture.PointedGeometricConvergence

theorem base_preserving_at_time
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ioo T' T) :
    (G.embedding j).toFun (t, G.limitFlow.base) =
      (t, (S.flow (G.subsequence j)).base) := by
  apply Prod.ext
  · exact (G.embedding j).time_preserving t G.limitFlow.base
  · have hbase := congrArg Prod.snd (G.base_preserving j)
    exact ((G.embedding j).spatial_eq_of_mem (s := t) (t := 0) ht hT
      (G.base_in_exhaustion j)).trans hbase

end PoincareConjecture.PointedGeometricConvergence
