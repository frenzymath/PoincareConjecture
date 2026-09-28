import PoincareConjecture.Proofs.M10.SegmentDistance

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]

set_option backward.isDefEq.respectTransparency false in

theorem inverseChart_local_lipschitz (g : RiemannianMetric n M) (q : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (extChartAt (𝓡 n) q q) r ⊆ (extChartAt (𝓡 n) q).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C (extChartAt (𝓡 n) q).symm
        (Metric.ball (extChartAt (𝓡 n) q q) r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let (x : EuclideanSpace ℝ (Fin n)) : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    normedAddCommGroupTangentSpaceVectorSpace x
  let (x : EuclideanSpace ℝ (Fin n)) : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    normedSpaceTangentSpaceVectorSpace x
  obtain ⟨C, hC, hbound⟩ := eventually_norm_mfderivWithin_symm_extChartAt_lt (𝓡 n) q
  have hbound' : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) q q),
      ‖mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm y‖ < C := by
    simpa only [modelWithCornersSelf_coe, range_id, nhdsWithin_univ, mfderivWithin_univ]
      using hbound
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (extChartAt_target_mem_nhds (I := 𝓡 n) q) hbound')
  have htarget : Metric.ball (extChartAt (𝓡 n) q q) r ⊆ (extChartAt (𝓡 n) q).target :=
    fun y hy ↦ (hrsub hy).1
  refine ⟨r, hr, htarget, ⟨C, hC.le⟩, ?_⟩
  intro x hx y hy
  apply riemannianEDist_le_of_differential_bound g (convex_ball _ _) Metric.isOpen_ball
    ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := 1) q).mono htarget) ?_ hx hy
  intro z hz v
  have hvnorm : ‖mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z v‖ =
      g.tangentNorm ((extChartAt (𝓡 n) q).symm z)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z v) :=
    norm_eq_sqrt_real_inner _
  rw [← hvnorm]
  exact (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right (hrsub hz).2.le (norm_nonneg _))

end PoincareConjecture.M10
