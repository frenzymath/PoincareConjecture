import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Lipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_intrinsic_lipschitz_chart_ball (g : RiemannianMetric n M) (a : M) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      Metric.ball (extChartAt (𝓡 n) a a) r ⊆ (extChartAt (𝓡 n) a).target ∧
      ∀ z ∈ Metric.ball (extChartAt (𝓡 n) a a) r,
      ∀ w ∈ Metric.ball (extChartAt (𝓡 n) a a) r,
        g.edist ((extChartAt (𝓡 n) a).symm z) ((extChartAt (𝓡 n) a).symm w) ≤
          (C : ℝ≥0∞) * EDist.edist z w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  obtain ⟨C, _, hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt (𝓡 n) a
  have hbound : ∀ᶠ z in 𝓝 (extChartAt (𝓡 n) a a),
      ‖mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm z‖ₑ < C := by
    simpa only [modelWithCornersSelf_coe, range_id, nhdsWithin_univ,
      mfderivWithin_univ] using hC
  have htarget : (extChartAt (𝓡 n) a).target ∈ 𝓝 (extChartAt (𝓡 n) a a) := by
    simpa only [modelWithCornersSelf_coe, range_id, nhdsWithin_univ] using
      extChartAt_target_mem_nhdsWithin (I := 𝓡 n) a
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hbound)
  refine ⟨C, r, hr, fun z hz ↦ (hball hz).1, fun z hz w hw ↦ ?_⟩
  apply Poincare.riemannianEDist_le_mul_edist_of_convex (convex_ball _ _) ?_ ?_ hz hw
  · intro y hy
    simpa only [modelWithCornersSelf_coe, range_id, contMDiffWithinAt_univ] using
      contMDiffWithinAt_extChartAt_symm_range (I := 𝓡 n) (n := 1) a (hball hy).1
  · exact fun y hy ↦ (hball hy).2.le



theorem exists_chart_weakPartials_of_distance_lipschitz
    (g : RiemannianMetric n M) {f : M → ℝ}
    (hf : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal) (a : M) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (extChartAt (𝓡 n) a a) r ⊆ (extChartAt (𝓡 n) a).target ∧
      (∀ K, IsCompact K → K ⊆ Metric.ball (extChartAt (𝓡 n) a a) r →
        MemLp (fun x => f ((extChartAt (𝓡 n) a).symm x)) 2 (volume.restrict K)) ∧
      ∃ p : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ i K, IsCompact K → K ⊆ Metric.ball (extChartAt (𝓡 n) a a) r →
          MemLp (p i) 2 (volume.restrict K)) ∧
        ∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (p i)
          (fun x => f ((extChartAt (𝓡 n) a).symm x))
          (Metric.ball (extChartAt (𝓡 n) a a) r) := by
  obtain ⟨C, r, hr, hball, hdist⟩ := g.exists_intrinsic_lipschitz_chart_ball a
  have hLip : LipschitzOnWith C (fun x => f ((extChartAt (𝓡 n) a).symm x))
      (Metric.ball (extChartAt (𝓡 n) a a) r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hreal := ENNReal.toReal_mono (by finiteness) (hdist x hx y hy)
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at hreal
    exact (hf _ _).trans hreal
  obtain ⟨hL2, p, hp, hw⟩ :=
    Poincare.Analysis.Sobolev.Weak.exists_weakPartials_of_lipschitzOn Metric.isOpen_ball hLip
  exact ⟨r, hr, hball, hL2, p, hp, hw⟩

end PoincareConjecture.RiemannianMetric
