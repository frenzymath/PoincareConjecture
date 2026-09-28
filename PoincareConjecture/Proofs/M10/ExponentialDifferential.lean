import PoincareConjecture.Proofs.M10.ExponentialSlice
import PoincareConjecture.Proofs.M10.EndpointCoordinates
import PoincareConjecture.Proofs.M10.SmoothMetric
import PoincareConjecture.Proofs.M10.PullbackMetric









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponentialSliceChart_differential (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (x v : EuclideanSpace ℝ (Fin n)) :
    mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x v =
      G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
        (metricCoordinates (F.metric T) p v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := (metricCoordinates (F.metric T) p).toContinuousLinearEquiv
  have htime : (β x, τ) ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hγ := G.gamma_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds htime)
  have hs : MDifferentiableAt 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n)
      (fun Z ↦ G.gamma Z τ) (β x) :=
    (hγ.comp (β x) (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
  have heq : (exponentialSliceChart G τ : EuclideanSpace ℝ (Fin n) → M) =
      (fun Z ↦ G.gamma Z τ) ∘ β := by
    funext y
    exact exponentialSliceChart_apply G τ y
  rw [heq]
  have hc := mfderiv_comp_apply x hs β.differentiableAt.mdifferentiableAt v
  rw [mfderiv_eq_fderiv, β.fderiv] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in

theorem exponentialSlice_pullbackMetric_eq (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) (x : EuclideanSpace ℝ (Fin n))
    (q₀ : M)
    (hq : G.gamma (metricCoordinates (F.metric T) p x) τ ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source)
    (u v : EuclideanSpace ℝ (Fin n)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    let z := (metricCoordinates (F.metric T) p x, τ)
    pullbackMetricForm (F.metric (T - τ)) (exponentialSliceChart G τ) x u v =
      coordinateBackwardMetric F T q₀ (endpointCoordinates G q₀ z, τ)
        (fderiv ℝ (endpointCoordinates G q₀) z (metricCoordinates (F.metric T) p u, 0))
        (fderiv ℝ (endpointCoordinates G q₀) z (metricCoordinates (F.metric T) p v, 0)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let z := (metricCoordinates (F.metric T) p x, τ)
  have hz : z ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  change (F.metric (T - τ)).inner (exponentialSliceChart G τ x)
      (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x u)
      (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x v) = _
  rw [exponentialSliceChart_differential G hτ hmax x u,
    exponentialSliceChart_differential G hτ hmax x v, exponentialSliceChart_apply,
    endpointCoordinates_horizontal G q₀ z hz hq,
    endpointCoordinates_horizontal G q₀ z hz hq]
  have hq' : G.gamma z.1 z.2 ∈ (extChartAt (𝓡 n) q₀).source := by
    simpa only [extChartAt_source] using hq
  dsimp only [coordinateBackwardMetric, endpointCoordinates]
  rw [(extChartAt (𝓡 n) q₀).left_inv hq']
  exact (backwardMetricCoordinates_apply q₀ (G.gamma z.1 z.2, τ) hq
    (G.toLExponentialFamily.sliceDifferential z.1 τ (metricCoordinates (F.metric T) p u))
    (G.toLExponentialFamily.sliceDifferential z.1 τ (metricCoordinates (F.metric T) p v))).symm

end PoincareConjecture.M10
