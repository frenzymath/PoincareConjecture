import PoincareConjecture.Proofs.M10.ChartLipschitz








set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]

set_option backward.isDefEq.respectTransparency false in

theorem locallyLipschitz_in_coordinates (g : RiemannianMetric n M) {f : M → ℝ}
    (hf :
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      LocallyLipschitz f) (q : M) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsOpen S ∧ extChartAt (𝓡 n) q q ∈ S ∧
      S ⊆ (extChartAt (𝓡 n) q).target ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (f ∘ (extChartAt (𝓡 n) q).symm) S := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change LocallyLipschitz f at hf
  obtain ⟨K, U, hU, hLip⟩ := hf q
  obtain ⟨r, hr, htarget, C, hchart⟩ := inverseChart_local_lipschitz g q
  have hpre : (extChartAt (𝓡 n) q).symm ⁻¹' U ∈ 𝓝 (extChartAt (𝓡 n) q q) := by
    apply (continuousAt_extChartAt_symm (I := 𝓡 n) q).preimage_mem_nhds
    simpa only [extChartAt_to_inv] using hU
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (Metric.ball_mem_nhds _ hr) hpre)
  refine ⟨Metric.ball (extChartAt (𝓡 n) q q) s, Metric.isOpen_ball,
    Metric.mem_ball_self hs, fun x hx ↦ htarget (hsub hx).1, K * C, ?_⟩
  exact hLip.comp (hchart.mono (fun _ hx ↦ (hsub hx).1))
    (fun _ hx ↦ (hsub hx).2)

end PoincareConjecture.M10
