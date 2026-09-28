import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Inverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Ricci

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_regular_radial_extension
    {e : EuclideanSpace ℝ (Fin n) → M}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (θ : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 ≤ t)
    (hsub : ∀ s ∈ Icc 0 t, s • θ ∈ U)
    (hi : ∀ s ∈ Icc 0 t,
      (mfderiv (𝓡 n) (𝓡 n) e (s • θ)).IsInvertible) :
    ∃ b : ℝ, t < b ∧
      (∀ s ∈ Icc 0 b, s • θ ∈ U) ∧
      ∀ s ∈ Icc 0 b,
        (mfderiv (𝓡 n) (𝓡 n) e (s • θ)).IsInvertible := by
  obtain ⟨B, htB, hBU, heB, hB, hBi⟩ := exists_smooth_inverse_branch
    hU he (hsub t ⟨ht, le_rfl⟩) (hi t ⟨ht, le_rfl⟩)
  have hnear : {s : ℝ | s • θ ∈ B.source} ∈ 𝓝 t :=
    (show ContinuousAt (fun s : ℝ => s • θ) t by fun_prop).preimage_mem_nhds
      (B.open_source.mem_nhds htB)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have htail : ∀ s ∈ Icc t (t + δ / 2), s • θ ∈ B.source := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    linarith [hs.2]
  have hdiff : B.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨hB.mdifferentiableOn (by simp), hBi.mdifferentiableOn (by simp)⟩
  refine ⟨t + δ / 2, by linarith, ?_, ?_⟩
  · intro s hs
    rcases le_total s t with hst | hts
    · exact hsub s ⟨hs.1, hst⟩
    · exact hBU (htail s ⟨hts, hs.2⟩)
  · intro s hs
    rcases le_total s t with hst | hts
    · exact hi s ⟨hs.1, hst⟩
    · have hsB := htail s ⟨hts, hs.2⟩
      have heq : e =ᶠ[𝓝 (s • θ)] B :=
        Filter.eventuallyEq_of_mem (B.open_source.mem_nhds hsB) heB
      rw [heq.mfderiv_eq]
      exact ⟨hdiff.mfderiv hsB, rfl⟩

end PoincareConjecture.RiemannianMetric
