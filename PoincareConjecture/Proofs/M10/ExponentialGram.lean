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

theorem exponential_gram_hasDerivAt
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    let q := G.gamma (metricCoordinates (F.metric T) p x) τ
    let V := fun i : Fin n ↦ G.toLExponentialFamily.sliceDifferential
      (metricCoordinates (F.metric T) p x) τ
      (metricCoordinates (F.metric T) p (C (EuclideanSpace.basisFun (Fin n) ℝ i)))
    ∃ D : Matrix (Fin n) (Fin n) ℝ,
      HasDerivAt (fun s ↦ (fun i j : Fin n ↦
        pullbackMetricForm (F.metric (T - s)) (exponentialSliceChart G s) x
          (C (EuclideanSpace.basisFun (Fin n) ℝ i))
          (C (EuclideanSpace.basisFun (Fin n) ℝ j)))) D τ ∧
      ∀ i, D i i = 2 * (F.connection (T - τ)).ricci q (V i) (V i) +
        2 * (F.connection (T - τ)).hessian (fun y ↦ reducedLength F T p y τ) q (V i) (V i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := metricCoordinates (F.metric T) p
  let z := (β x, τ)
  let q := G.gamma z.1 z.2
  let E := endpointCoordinates G q
  let B := coordinateBackwardMetric F T q
  let W := fun i : Fin n ↦ β (C (EuclideanSpace.basisFun (Fin n) ℝ i))
  let A := fun s ↦ (fun i j : Fin n ↦
    pullbackMetricForm (F.metric (T - s)) (exponentialSliceChart G s) x
      (C (EuclideanSpace.basisFun (Fin n) ℝ i))
      (C (EuclideanSpace.basisFun (Fin n) ℝ j)))
  obtain ⟨hτ, hmax, _, _⟩ := hreg.1
  have hz : z ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source :=
    mem_chart_source _ _
  have hE : ContDiffAt ℝ 2 E z :=
    (endpointCoordinates_contDiffAt G q z hz hq).of_le (by decide)
  have hB : DifferentiableAt ℝ B (E z, τ) :=
    (coordinateBackwardMetric_contDiffAt hwindow q hτ hmax).differentiableAt (by simp)
  have hγ := G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
  have hc : ContinuousAt (fun s ↦ G.gamma (β x) s) τ :=
    hγ.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  have hcoords (i j : Fin n) : (fun s ↦ A s i j) =ᶠ[𝓝 τ]
      (fun s ↦ B (E (z.1, s), s)
        (fderiv ℝ E (z.1, s) (W i, 0)) (fderiv ℝ E (z.1, s) (W j, 0))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hτ, hmax⟩,
      hc ((chartAt (EuclideanSpace ℝ (Fin n)) q).open_source.mem_nhds hq)]
      with s hs hqs
    exact exponentialSlice_pullbackMetric_eq G hs.1 hs.2 x q hqs
      (C (EuclideanSpace.basisFun (Fin n) ℝ i)) (C (EuclideanSpace.basisFun (Fin n) ℝ j))
  have hdiff (i j : Fin n) : DifferentiableAt ℝ (fun s ↦ A s i j) τ :=
    ((endpoint_gram_hasDerivAt hE hB (W i) (W j)).congr_of_eventuallyEq
      (hcoords i j)).differentiableAt
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ deriv (fun s ↦ A s i j) τ
  refine ⟨D, hasDerivAt_pi.mpr (fun i ↦ hasDerivAt_pi.mpr (fun j ↦
    (hdiff i j).hasDerivAt)), ?_⟩
  intro i
  have hd := (endpoint_gram_diagonal_hasDerivAt hwindow hL G z hreg (W i)).congr_of_eventuallyEq
    (hcoords i i)
  have hv : fderiv ℝ E z (W i, 0) = G.toLExponentialFamily.sliceDifferential z.1 τ (W i) := by
    rw [endpointCoordinates_horizontal G q z hz hq,
      TangentBundle.continuousLinearMapAt_trivializationAt hq, mfderiv_extChartAt_self]
    rfl
  have hd' : deriv (fun s ↦ A s i i) τ =
      2 * (F.connection (T - τ)).ricci q (fderiv ℝ E z (W i, 0)) (fderiv ℝ E z (W i, 0)) +
      2 * (F.connection (T - τ)).hessian (fun y ↦ reducedLength F T p y τ) q
        (fderiv ℝ E z (W i, 0)) (fderiv ℝ E z (W i, 0)) := hd.deriv
  rw [hv] at hd'
  exact hd'

end PoincareConjecture.M10
