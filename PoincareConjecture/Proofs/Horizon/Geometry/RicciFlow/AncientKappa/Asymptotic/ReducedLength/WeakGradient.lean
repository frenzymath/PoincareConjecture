import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakLaplacian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Lipschitz


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem reducedLength_coordinates_locallyLipschitz
    {R τ : ℝ} {p : M} (D : ReducedLengthMeasureData K.flow 0 R p)
    (hτ : 0 < τ) (hτR : τ < R)
    {e : EuclideanSpace ℝ (Fin n) → M} {V : Set (EuclideanSpace ℝ (Fin n))}
    (he : ∀ x ∈ V, ContinuousAt e x) {B : ℝ≥0}
    (hLip : ∀ x ∈ V, ∀ y ∈ V,
      (K.flow.metric 0).edist (e x) (e y) ≤ (B : ℝ≥0∞) * EDist.edist x y) :
    LocallyLipschitzOn V (fun x ↦ reducedLength K.flow 0 p (e x) τ) := by
  let g := K.flow.metric 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have heLip : LipschitzOnWith B e V := hLip
  have hpairLip : LipschitzOnWith B (fun x ↦ (e x, τ)) V := by
    simpa using heLip.prodMk (LipschitzWith.const τ).lipschitzOnWith
  have hlocD : LocallyLipschitzOn (univ ×ˢ Ioo 0 R)
      (fun z : M × ℝ ↦ reducedLength K.flow 0 p z.1 z.2) := D.locally_lipschitz
  intro x hx
  obtain ⟨L, W, hW, hWL⟩ := hlocD (x := (e x, τ)) ⟨mem_univ _, hτ, hτR⟩
  have hW' : W ∈ 𝓝 (e x, τ) := by
    rwa [nhdsWithin_eq_nhds.mpr ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ _, hτ, hτR⟩)] at hW
  refine ⟨L * B, V ∩ (fun y ↦ (e y, τ)) ⁻¹' W, ?_, ?_⟩
  · exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
      (((he x hx).prodMk continuousAt_const).preimage_mem_nhds hW'))
  · exact hWL.comp (hpairLip.mono inter_subset_left) (fun _ hy ↦ hy.2)

theorem reducedLength_lipschitz_coordinate_neighborhoods
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∀ a : M, ∃ U : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ U ∧
      U ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        ((fun q ↦ reducedLength K.flow 0 p q τ) ∘
          (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) U := by
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  intro a
  obtain ⟨B, r, hr, hball, hdist⟩ := (K.flow.metric 0).exists_intrinsic_lipschitz_chart_ball a
  have hloc := reducedLength_coordinates_locallyLipschitz D hτ (by linarith)
    (fun x hx ↦ ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) a (hball hx)).contMDiffAt
      (extChartAt_target_mem_nhds' (hball hx))).continuousAt) hdist
  obtain ⟨C, W, hW, hWL⟩ := hloc (Metric.mem_ball_self hr)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ hr)] at hW
  obtain ⟨U, hU, hUo, haU⟩ := mem_nhds_iff.mp (inter_mem hW (Metric.ball_mem_nhds _ hr))
  refine ⟨U, hUo, ?_, ?_, C, ?_⟩
  · simpa using haU
  · intro x hx
    simpa using hball (hU hx).2
  · simpa [Function.comp_def] using hWL.mono (fun x hx ↦ (hU hx).1)

theorem reducedLength_weak_gradient_le (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ q, 0 ≤ φ q) :
    Integrable (fun q ↦ mvfderiv (𝓡 n) (fun x ↦ reducedLength K.flow 0 p x τ) q
      ((K.flow.connection (0 - τ)).gradient φ q))
        (calibratedMetricVolume (K.flow.metric (0 - τ))) ∧
    -(∫ q, mvfderiv (𝓡 n) (fun x ↦ reducedLength K.flow 0 p x τ) q
      ((K.flow.connection (0 - τ)).gradient φ q)
        ∂calibratedMetricVolume (K.flow.metric (0 - τ))) ≤
      ∫ q, φ q * ((reducedLength K.flow 0 p q τ + (n : ℝ) / 2) / τ)
        ∂calibratedMetricVolume (K.flow.metric (0 - τ)) := by
  obtain ⟨X⟩ := (K.flow.metric 0).nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨X, X.isCompact, X.iUnion_eq⟩
  have hg := (K.flow.connection (0 - τ)).integral_mul_laplacian_of_locally_lipschitz
    (P.continuous_reducedLength p τ hτ)
    (P.reducedLength_lipschitz_coordinate_neighborhoods p hτ) hφ hφc
  have hw := P.reducedLength_weak_laplacian_le p hτ hφ hφc hφ0
  simp_rw [calibratedMetricVolume_eq_volumeMeasure] at hw ⊢
  exact ⟨hg.1, hg.2 ▸ hw⟩

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
