import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.PathCompactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ChartCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ChartH1
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.ReducedLengthMinimum

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]

noncomputable abbrev referenceMetricSpace (g : RiemannianMetric n M) : MetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  EMetricSpace.toMetricSpace (g.edist_ne_top)

end PoincareConjecture.ReducedLengthMinimum

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum
open ReducedLengthMinimum.Variational

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_spatial_minimizing_uniform_limit (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    letI : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
    ∃ (paths : ℕ → BackwardTimePath K.flow 0 0 τ) (γ : ℝ → M),
      (∀ k, (paths k).curve 0 = p) ∧
      Antitone (fun k ↦ backwardLLength K.flow 0 0 τ (paths k).curve) ∧
      Tendsto (fun k ↦ backwardLLength K.flow 0 0 τ (paths k).curve) atTop
        (𝓝 (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ)) ∧
      Continuous γ ∧ γ 0 = p ∧
      TendstoUniformlyOn (fun k s ↦ (paths k).curve (s ^ 2)) γ atTop (Icc 0 (Real.sqrt τ)) ∧
      ∀ k, IntervalIntegrable
          (referenceSpeedSq (K.flow.metric 0) (fun s ↦ (paths k).curve (s ^ 2)))
          volume 0 (Real.sqrt τ) ∧
        (∫ s in 0..Real.sqrt τ,
          referenceSpeedSq (K.flow.metric 0) (fun r ↦ (paths k).curve (r ^ 2)) s) ≤
            2 * backwardLLength K.flow 0 0 τ (paths 0).curve := by
  letI : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
  obtain ⟨paths, α, hstart, hanti, haction, hα0, huniform⟩ :=
    K.exists_uniformly_convergent_spatial_minimizing_paths p hτ
  let γ : ℝ → M := fun s ↦ α (projIcc 0 (Real.sqrt τ) (Real.sqrt_nonneg τ) s)
  have hγ : Continuous γ := α.continuous.comp continuous_projIcc
  have hγ0 : γ 0 = p := by simpa only [γ, projIcc_left] using hα0
  have hlim : TendstoUniformlyOn (fun k s ↦ (paths k).curve (s ^ 2)) γ atTop
      (Icc 0 (Real.sqrt τ)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := huniform ε hε
    filter_upwards [eventually_ge_atTop N] with k hk
    intro s hs
    have h := hN k hk ⟨s, hs⟩
    rw [dist_comm]
    change dist ((paths k).curve (s ^ 2)) (γ s) < ε
    change ((K.flow.metric 0).edist ((paths k).curve (s ^ 2))
      (α (projIcc 0 (Real.sqrt τ) (Real.sqrt_nonneg τ) s))).toReal < ε
    rw [projIcc_of_mem _ hs]
    exact h
  refine ⟨paths, γ, hstart, hanti, haction, hγ, hγ0, hlim, ?_⟩
  intro k
  have hweighted := K.surface_referenceWeightedEnergy_bound (paths k)
  have henergy := squarePath_referenceEnergy (paths k) (K.flow.metric 0) hweighted.1
  refine ⟨henergy.1, ?_⟩
  rw [henergy.2]
  exact mul_le_mul_of_nonneg_left
    (hweighted.2.trans (hanti (Nat.zero_le k))) (by norm_num)

theorem exists_spatial_minimizing_chart_limit (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    letI : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
    ∃ (paths : ℕ → BackwardTimePath K.flow 0 0 τ) (γ : ℝ → M)
      (m : ℕ) (t : Fin (m + 1) → ℝ) (x : Fin m → M) (Q : Fin m → Set M)
      (v : ∀ i : Fin m, ℕ → IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ))
      (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ))
      (B : Fin m → ℝ),
      (∀ k, (paths k).curve 0 = p) ∧
      Antitone (fun k ↦ backwardLLength K.flow 0 0 τ (paths k).curve) ∧
      Tendsto (fun k ↦ backwardLLength K.flow 0 0 τ (paths k).curve) atTop
        (𝓝 (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ)) ∧
      Continuous γ ∧ γ 0 = p ∧
      TendstoUniformlyOn (fun k s ↦ (paths k).curve (s ^ 2)) γ atTop (Icc 0 (Real.sqrt τ)) ∧
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last m) = Real.sqrt τ ∧
      (∀ i, IsCompact (Q i) ∧
        γ '' Icc (t i.castSucc) (t i.succ) ⊆ interior (Q i) ∧
        Q i ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source) ∧
      (∀ i k, MapsTo (fun s ↦ (paths k).curve (s ^ 2))
        (Icc (t i.castSucc) (t i.succ)) (Q i)) ∧
      (∀ i k, ‖v i k‖ ≤ B i ∧
        (v i k : ℝ → EuclideanSpace ℝ (Fin 2)) =ᵐ[volume.restrict
          (Icc (t i.castSucc) (t i.succ))]
          deriv ((extChartAt (𝓡 2) (x i)) ∘ (fun s ↦ (paths k).curve (s ^ 2)))) ∧
      (∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
        extChartAt (𝓡 2) (x i) (γ s) = extChartAt (𝓡 2) (x i) (γ (t i.castSucc)) +
          ∫ r in t i.castSucc..s, w i r) ∧
      ∀ i, ∀ l : IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ) →L[ℝ] ℝ,
        Tendsto (fun k ↦ l (v i k)) atTop (𝓝 (l (w i))) := by
  classical
  letI : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
  letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡 2)
  obtain ⟨paths, γ, hstart, hanti, haction, hγ, hγ0, hlim, hE⟩ :=
    K.exists_spatial_minimizing_uniform_limit p hτ
  obtain ⟨m, t, x, Q, N, ht, ht0, htend, hQ, htail⟩ :=
    exists_compact_partition_of_uniform_limit
      (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
      (fun x ↦ (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source)
      (fun y ↦ ⟨y, mem_chart_source _ y⟩) (Real.sqrt_nonneg τ) γ hγ
      (fun k s ↦ (paths k).curve (s ^ 2)) hlim
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hleft (i : Fin m) : 0 ≤ t i.castSucc := by
    rw [← ht0]
    exact ht (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ Real.sqrt τ := by
    rw [← htend]
    exact ht (Fin.le_last _)
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc 0 (Real.sqrt τ) :=
    Icc_subset_Icc (hleft i) (hright i)
  have hsuboo (i : Fin m) : Ioo (t i.castSucc) (t i.succ) ⊆ Ioo 0 (Real.sqrt τ) :=
    Ioo_subset_Ioo (hleft i) (hright i)
  let q : ℕ → BackwardTimePath K.flow 0 0 τ := fun k ↦ paths (k + N)
  let α : ℕ → ℝ → M := fun k s ↦ (q k).curve (s ^ 2)
  have hshift : StrictMono (fun k : ℕ ↦ k + N) := fun _ _ hij ↦ Nat.add_lt_add_right hij N
  have hlimq : TendstoUniformlyOn α γ atTop (Icc 0 (Real.sqrt τ)) := by
    intro U hU
    exact hshift.tendsto_atTop.eventually (hlim U hU)
  have hα (i : Fin m) (k : ℕ) : ContinuousOn (α k) (Icc (t i.castSucc) (t i.succ)) := by
    apply (q k).continuous.comp (continuous_id.pow 2).continuousOn
    intro s hs
    exact ⟨sq_nonneg s, (Real.le_sqrt (hsub i hs).1 hτ.le).mp (hsub i hs).2⟩
  have hreg (i : Fin m) (k : ℕ) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) 1 (α k) (Ioo (t i.castSucc) (t i.succ)) := by
    apply (q k).regular.comp ((contDiff_id.pow 2).contMDiff.contMDiffOn)
    intro s hs
    exact ⟨sq_pos_of_pos (hsuboo i hs).1,
      (Real.lt_sqrt (hsuboo i hs).1.le).mp (hsuboo i hs).2⟩
  have hαQ (i : Fin m) (k : ℕ) : MapsTo (α k) (Icc (t i.castSucc) (t i.succ)) (Q i) :=
    htail (k + N) (Nat.le_add_left N k) i
  have hγQ (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ)) (Q i) :=
    fun s hs ↦ interior_subset ((hQ i).2.1 (mem_image_of_mem γ hs))
  have hEpiece (i : Fin m) (k : ℕ) : IntervalIntegrable
      (referenceSpeedSq (K.flow.metric 0) (α k)) volume (t i.castSucc) (t i.succ) := by
    apply (hE (k + N)).1.mono_set
    simpa only [uIcc_of_le (hseg i), uIcc_of_le (Real.sqrt_nonneg τ)] using hsub i
  have hEbound (i : Fin m) (k : ℕ) :
      (∫ s in t i.castSucc..t i.succ, referenceSpeedSq (K.flow.metric 0) (α k) s) ≤
        2 * backwardLLength K.flow 0 0 τ (paths 0).curve := by
    apply le_trans _ (hE (k + N)).2
    exact intervalIntegral.integral_mono_interval (hleft i) (hseg i) (hright i)
      (Eventually.of_forall (referenceSpeedSq_nonneg _ _)) (hE (k + N)).1
  obtain ⟨v, w, B, φ, hφ, hv, hprimitive, hweak⟩ :=
    finite_chartH1_limit (K.flow.metric 0)
      (fun i ↦ t i.castSucc) (fun i ↦ t i.succ) hseg x Q
      (fun i ↦ (hQ i).1) (fun i ↦ (hQ i).2.2) α γ hα hreg hαQ hγQ
      (fun i s hs ↦ hlimq.tendsto_at (hsub i hs)) hEpiece
      (fun _ ↦ 2 * backwardLLength K.flow 0 0 τ (paths 0).curve) hEbound
  have hselected : StrictMono (fun k ↦ φ k + N) := hshift.comp hφ
  refine ⟨q ∘ φ, γ, m, t, x, Q, (fun i k ↦ v i (φ k)), w, B,
    (fun k ↦ hstart (φ k + N)), ?_, ?_, hγ, hγ0, ?_, ht, ht0, htend, hQ,
    (fun i k ↦ hαQ i (φ k)), (fun i k ↦ hv i (φ k)), hprimitive, hweak⟩
  · exact hanti.comp_monotone hselected.monotone
  · exact haction.comp hselected.tendsto_atTop
  · intro U hU
    exact hφ.tendsto_atTop.eventually (hlimq U hU)

end PoincareConjecture.AncientKappaSolution
