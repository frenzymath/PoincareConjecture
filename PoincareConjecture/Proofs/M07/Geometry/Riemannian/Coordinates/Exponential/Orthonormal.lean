import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Orthonormal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_orthonormal_exponential_of_precompact_ball
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    ∃ L : E ≃L[ℝ] E, ∃ e : E → M,
      (∀ v w, B (c p) (L v) (L w) = inner ℝ v w) ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
      HasFDerivAt (fun v => c (e v)) L.toContinuousLinearMap 0 ∧
      ∀ v ∈ Metric.ball 0 R, ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
        HasDerivAt (fun t => c (γ t)) (L v) 0 ∧ γ 1 = e v ∧
        (∀ t ∈ Ioo (-ε) (1 + ε),
          g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) = ‖v‖) ∧
        (∀ t ∈ Ioo (-ε) (1 + ε),
          g.edist p (γ t) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal |t|) := by
  dsimp only
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  obtain ⟨f, hf, hf0, hfd, hgeo⟩ :=
    g.exists_exponential_of_precompact_ball p hR hcompact
  have hnorm (v : EuclideanSpace ℝ (Fin n)) :
      Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) (L v) (L v)) = ‖v‖ := by
    rw [hL, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]
  have hmaps : MapsTo L (Metric.ball 0 R)
      {v | Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) v v) < R} := by
    intro v hv
    simpa only [mem_ofPred_eq, hnorm, Metric.mem_ball, dist_zero_right] using hv
  refine ⟨L, f ∘ L, hL, ?_, ?_, ?_, ?_⟩
  · exact hf.comp (contMDiff_iff_contDiff.mpr L.contDiff).contMDiffOn hmaps
  · simpa only [Function.comp_apply, map_zero] using hf0
  · have hfd' : HasFDerivAt (fun v => extChartAt (𝓡 n) p (f v))
        (ContinuousLinearMap.id ℝ _) (L 0) := by
      simpa only [map_zero] using hfd
    have hd := hfd'.comp 0 L.hasFDerivAt
    simpa only [map_zero, ContinuousLinearMap.id_comp, Function.comp_def] using hd
  · intro v hv
    obtain ⟨ε, hε, γ, hγ, hp, hd, hend, _⟩ := hgeo (L v) (hmaps hv)
    have hzero : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by
      constructor <;> linarith
    obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (hzero.1.trans hzero.2)
    have hC0 := hC 0 hzero
    rw [hγ.tangentNorm_initial hzero hp hd, hnorm] at hC0
    refine ⟨ε, hε, γ, hγ, hp, hd, hend, ?_, ?_⟩
    · intro t ht
      exact (hC t ht).trans hC0.symm
    · intro t ht
      simpa only [hnorm] using hγ.edist_le_initial_speed hzero hp hd ht

end PoincareConjecture.RiemannianMetric
