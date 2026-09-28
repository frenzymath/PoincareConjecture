import PoincareConjecture.Proofs.M10.ExponentialGram
import PoincareConjecture.Proofs.M10.ExponentialNormalization
import PoincareConjecture.Proofs.M10.GramNormalization
import PoincareConjecture.Proofs.M10.MetricTrace
import PoincareConjecture.Proofs.M10.JacobianEvolution

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponentialJacobian_hasDerivAt
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain) :
    HasDerivAt (fun s ↦ pullbackJacobian (F.metric (T - s)) (exponentialSliceChart G s) x)
      (pullbackJacobian (F.metric (T - τ)) (exponentialSliceChart G τ) x *
        ((F.connection (T - τ)).scalarCurvature (exponentialSliceChart G τ x) +
          (F.connection (T - τ)).laplacian (fun y ↦ reducedLength F T p y τ)
            (exponentialSliceChart G τ x))) τ := by
  obtain ⟨C, hC⟩ := exists_exponential_source_normalization G x hreg
  let q := G.gamma (metricCoordinates (F.metric T) p x) τ
  let A : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s ↦ (fun i j : Fin n ↦
    pullbackMetricForm (F.metric (T - s)) (exponentialSliceChart G s) x
      (C (EuclideanSpace.basisFun (Fin n) ℝ i))
      (C (EuclideanSpace.basisFun (Fin n) ℝ j)))
  let j := fun s ↦ pullbackJacobian (F.metric (T - s)) (exponentialSliceChart G s) x
  obtain ⟨D, hA, hdiag⟩ := exponential_gram_hasDerivAt hwindow hL G x hreg C.toContinuousLinearMap
  have hAt : A τ = 1 := by
    ext i j
    change (F.metric (T - τ)).inner (exponentialSliceChart G τ x)
      (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x
        (C (EuclideanSpace.basisFun (Fin n) ℝ i)))
      (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x
        (C (EuclideanSpace.basisFun (Fin n) ℝ j))) = (1 : Matrix (Fin n) (Fin n) ℝ) i j
    obtain ⟨hτ, hmax, _, _⟩ := hreg.1
    rw [exponentialSliceChart_differential G hτ hmax,
      exponentialSliceChart_differential G hτ hmax, exponentialSliceChart_apply,
      hC, hC, metricCoordinates_basis_inner, Matrix.one_apply]
  have hscale : (fun s ↦ C.toLinearMap.normDet * j s) =ᶠ[𝓝 τ]
      (fun s ↦ Real.sqrt ((A s).det)) := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [A, j, mul_comm] using!
      (sqrt_det_pullbackMetric_change_source (F.metric (T - s))
        (exponentialSliceChart G s) x C.toLinearMap).symm
  have hdiag' (i : Fin n) : D i i =
      2 * (F.connection (T - τ)).ricci q
        (metricCoordinates (F.metric (T - τ)) q (EuclideanSpace.basisFun (Fin n) ℝ i))
        (metricCoordinates (F.metric (T - τ)) q (EuclideanSpace.basisFun (Fin n) ℝ i)) +
      2 * (F.connection (T - τ)).hessian (fun y ↦ reducedLength F T p y τ) q
        (metricCoordinates (F.metric (T - τ)) q (EuclideanSpace.basisFun (Fin n) ℝ i))
        (metricCoordinates (F.metric (T - τ)) q (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    have hh := hdiag i
    change D i i =
      2 * (F.connection (T - τ)).ricci q
        (G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
          (metricCoordinates (F.metric T) p (C (EuclideanSpace.basisFun (Fin n) ℝ i))))
        (G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
          (metricCoordinates (F.metric T) p (C (EuclideanSpace.basisFun (Fin n) ℝ i)))) +
      2 * (F.connection (T - τ)).hessian (fun y ↦ reducedLength F T p y τ) q
        (G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
          (metricCoordinates (F.metric T) p (C (EuclideanSpace.basisFun (Fin n) ℝ i))))
        (G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
          (metricCoordinates (F.metric T) p (C (EuclideanSpace.basisFun (Fin n) ℝ i)))) at hh
    rw [hC] at hh
    exact hh
  have htrace : D.trace / 2 = (F.connection (T - τ)).scalarCurvature q +
      (F.connection (T - τ)).laplacian (fun y ↦ reducedLength F T p y τ) q := by
    change (∑ i : Fin n, D i i) / 2 = _
    simp_rw [hdiag']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_metricCoordinates_ricci, sum_metricCoordinates_hessian]
    ring
  have hd := hasDerivAt_jacobian_of_scaled_normalized_gram
    (ne_of_gt (source_normalization_normDet_pos C)) hscale hA hAt
  rw [htrace] at hd
  simpa only [exponentialSliceChart_apply] using hd

end PoincareConjecture.M10
