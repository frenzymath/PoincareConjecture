import PoincareConjecture.Proofs.M47.TerminalCommonIntervalDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u v

namespace PoincareConjecture.M47

theorem terminalCommonInterval_inverse_capture_distance
    {N : Type u} {X : Type v} [TopologicalSpace N] [TopologicalSpace X]
    [T3Space N] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (k : RiemannianMetric 3 N) (h : RiemannianMetric 3 X) (hk : MetricComplete k)
    (f : OpenPartialHomeomorph N X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f f.source)
    (hfi : ContMDiffOn (𝓡 3) (𝓡 3) 1 f.symm f.target)
    (q : N) {D : ℝ} (hD : 0 < D)
    (hsource : {z | k.edist q z ≤ ENNReal.ofReal (4 * (2 * D + 1))} ⊆ f.source)
    (hbound : ∀ z, k.edist q z ≤ ENNReal.ofReal (4 * (2 * D + 1)) →
      ∀ v : TangentSpace (𝓡 3) z,
        (1 / 2 : ℝ) * k.tangentNorm z v ≤
          h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ∧
        h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ 2 * k.tangentNorm z v) :
    (∀ y ∈ h.ball (f q) D, y ∈ f.target ∧ f.symm y ∈ k.ball q (2 * D)) ∧
      ∀ y ∈ h.ball (f q) D, ∀ z ∈ h.ball (f q) D,
        k.edist (f.symm y) (f.symm z) ≤ (2 : ℝ≥0∞) * h.edist y z := by
  have hsub (z : N) (hz : k.edist q z ≤ ENNReal.ofReal (4 * D)) :
      k.edist q z ≤ ENNReal.ofReal (4 * (2 * D + 1)) :=
    hz.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hcapture := terminalCommonInterval_capture_of_closed_buffer k h hk f hf hfi q
    (by positivity : 0 < 4 * D) (by norm_num : (0 : ℝ) < 2)
    (by linarith : 2 * D < 4 * D) (fun z hz => hsource (hsub z hz))
    (fun z hz v => by linarith only [(hbound z (hsub z hz) v).1])
  have hcaptured (y : X) (hy : y ∈ h.ball (f q) D) :
      y ∈ f.target ∧ f.symm y ∈ k.ball q (2 * D) := by
    obtain ⟨z, hz, rfl⟩ := hcapture hy
    have hzs : z ∈ f.source := hsource
      (hz.le.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    exact ⟨f.map_source hzs, by rwa [f.left_inv hzs]⟩
  refine ⟨hcaptured, ?_⟩
  have hcomparison := terminalCommonInterval_buffered_distance k h hk f hf hfi q
    (by positivity : 0 < 2 * D) (by norm_num : (0 : ℝ) < 1 / 2)
    hsource (by simpa only [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num] using hbound)
  intro y hy z hz
  have hpair := (hcomparison (f.symm y) (hcaptured y hy).2.le
    (f.symm z) (hcaptured z hz).2.le).1
  rw [f.right_inv (hcaptured y hy).1, f.right_inv (hcaptured z hz).1] at hpair
  calc
    _ = (2 : ℝ≥0∞) * (ENNReal.ofReal (1 / 2 : ℝ) *
        k.edist (f.symm y) (f.symm z)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_ofNat,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    _ ≤ _ := by gcongr

end PoincareConjecture.M47
