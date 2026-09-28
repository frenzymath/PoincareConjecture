import PoincareConjecture.Proofs.M10.EndpointGram
import PoincareConjecture.Proofs.M10.ExponentialDifferential









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponential_diagonal_hasDerivAt
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x v : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain) :
    let q := G.gamma (metricCoordinates (F.metric T) p x) τ
    let V := G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
      (metricCoordinates (F.metric T) p v)
    HasDerivAt (fun s ↦
      pullbackMetricForm (F.metric (T - s)) (exponentialSliceChart G s) x v v)
      (2 * (F.connection (T - τ)).ricci q V V +
        2 * (F.connection (T - τ)).hessian (fun y ↦ reducedLength F T p y τ) q V V) τ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := metricCoordinates (F.metric T) p
  let z := (β x, τ)
  let q := G.gamma z.1 z.2
  let E := endpointCoordinates G q
  let B := coordinateBackwardMetric F T q
  obtain ⟨hτ, hmax, _, _⟩ := hreg.1
  have hz : z ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source :=
    mem_chart_source _ _
  have hγ := G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
  have hc : ContinuousAt (fun s ↦ G.gamma (β x) s) τ :=
    hγ.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  have hcoords : (fun s ↦
      pullbackMetricForm (F.metric (T - s)) (exponentialSliceChart G s) x v v) =ᶠ[𝓝 τ]
      (fun s ↦ B (E (z.1, s), s)
        (fderiv ℝ E (z.1, s) (β v, 0)) (fderiv ℝ E (z.1, s) (β v, 0))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hτ, hmax⟩,
      hc ((chartAt (EuclideanSpace ℝ (Fin n)) q).open_source.mem_nhds hq)]
      with s hs hqs
    exact exponentialSlice_pullbackMetric_eq G hs.1 hs.2 x q hqs v v
  have hd := (endpoint_gram_diagonal_hasDerivAt hwindow hL G z hreg (β v)).congr_of_eventuallyEq
    hcoords
  have hv : fderiv ℝ E z (β v, 0) = G.toLExponentialFamily.sliceDifferential z.1 τ (β v) := by
    rw [endpointCoordinates_horizontal G q z hz hq,
      TangentBundle.continuousLinearMapAt_trivializationAt hq, mfderiv_extChartAt_self]
    rfl
  change HasDerivAt _
    (2 * (F.connection (T - τ)).ricci q (fderiv ℝ E z (β v, 0)) (fderiv ℝ E z (β v, 0)) +
      2 * (F.connection (T - τ)).hessian (fun y ↦ reducedLength F T p y τ) q
        (fderiv ℝ E z (β v, 0)) (fderiv ℝ E z (β v, 0))) τ at hd
  rw [hv] at hd
  exact hd

end PoincareConjecture.M10
